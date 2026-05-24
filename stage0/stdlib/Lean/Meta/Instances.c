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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_range(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
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
uint8_t lean_is_class(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value)}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "cannot find synthesization order for instance "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " with type"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "\nall remaining arguments have metavariables:"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_addInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` must be marked with `@[reducible]` or `@[implicit_reducible]`"};
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(lean_object* v_n_150_, lean_object* v_k_151_, lean_object* v_v_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_n_150_, v___x_153_, v_k_151_, v_v_152_);
return v___x_154_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; uint64_t v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1723u);
v___x_156_ = lean_uint64_of_nat(v___x_155_);
return v___x_156_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; 
v___x_157_ = ((size_t)5ULL);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_shift_left(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; 
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0);
v___x_162_ = lean_usize_sub(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(lean_object* v_x_164_, size_t v_x_165_, size_t v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_es_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v_j_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_es_169_ = lean_ctor_get(v_x_164_, 0);
v___x_170_ = ((size_t)5ULL);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_173_ = lean_usize_land(v_x_165_, v___x_172_);
v_j_174_ = lean_usize_to_nat(v___x_173_);
v___x_175_ = lean_array_get_size(v_es_169_);
v___x_176_ = lean_nat_dec_lt(v_j_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v_j_174_);
lean_dec(v_x_168_);
lean_dec(v_x_167_);
return v_x_164_;
}
else
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_213_; 
lean_inc_ref(v_es_169_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_x_164_, 0);
lean_dec(v_unused_214_);
v___x_178_ = v_x_164_;
v_isShared_179_ = v_isSharedCheck_213_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_x_164_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_213_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_v_180_; lean_object* v___x_181_; lean_object* v_xs_x27_182_; lean_object* v___y_184_; 
v_v_180_ = lean_array_fget(v_es_169_, v_j_174_);
v___x_181_ = lean_box(0);
v_xs_x27_182_ = lean_array_fset(v_es_169_, v_j_174_, v___x_181_);
switch(lean_obj_tag(v_v_180_))
{
case 0:
{
lean_object* v_key_189_; lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_key_189_ = lean_ctor_get(v_v_180_, 0);
v_val_190_ = lean_ctor_get(v_v_180_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_v_180_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v_v_180_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_inc(v_key_189_);
lean_dec(v_v_180_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_name_eq(v_x_167_, v_key_189_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_del_object(v___x_192_);
v___x_195_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_189_, v_val_190_, v_x_167_, v_x_168_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
v___y_184_ = v___x_196_;
goto v___jp_183_;
}
else
{
lean_object* v___x_198_; 
lean_dec(v_val_190_);
lean_dec(v_key_189_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v_x_168_);
lean_ctor_set(v___x_192_, 0, v_x_167_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_x_167_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_x_168_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v___y_184_ = v___x_198_;
goto v___jp_183_;
}
}
}
}
case 1:
{
lean_object* v_node_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_211_; 
v_node_201_ = lean_ctor_get(v_v_180_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_v_180_);
if (v_isSharedCheck_211_ == 0)
{
v___x_203_ = v_v_180_;
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_node_201_);
lean_dec(v_v_180_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_205_ = lean_usize_shift_right(v_x_165_, v___x_170_);
v___x_206_ = lean_usize_add(v_x_166_, v___x_171_);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_node_201_, v___x_205_, v___x_206_, v_x_167_, v_x_168_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_207_);
v___x_209_ = v___x_203_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
v___y_184_ = v___x_209_;
goto v___jp_183_;
}
}
}
default: 
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_x_167_);
lean_ctor_set(v___x_212_, 1, v_x_168_);
v___y_184_ = v___x_212_;
goto v___jp_183_;
}
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = lean_array_fset(v_xs_x27_182_, v_j_174_, v___y_184_);
lean_dec(v_j_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_185_);
v___x_187_ = v___x_178_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
else
{
lean_object* v_ks_215_; lean_object* v_vs_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_236_; 
v_ks_215_ = lean_ctor_get(v_x_164_, 0);
v_vs_216_ = lean_ctor_get(v_x_164_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_236_ == 0)
{
v___x_218_ = v_x_164_;
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_vs_216_);
lean_inc(v_ks_215_);
lean_dec(v_x_164_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_ks_215_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_vs_216_);
v___x_221_ = v_reuseFailAlloc_235_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v_newNode_222_; uint8_t v___y_224_; size_t v___x_230_; uint8_t v___x_231_; 
v_newNode_222_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v___x_221_, v_x_167_, v_x_168_);
v___x_230_ = ((size_t)7ULL);
v___x_231_ = lean_usize_dec_le(v___x_230_, v_x_166_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_222_);
v___x_233_ = lean_unsigned_to_nat(4u);
v___x_234_ = lean_nat_dec_lt(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
v___y_224_ = v___x_234_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___x_231_;
goto v___jp_223_;
}
v___jp_223_:
{
if (v___y_224_ == 0)
{
lean_object* v_ks_225_; lean_object* v_vs_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_ks_225_ = lean_ctor_get(v_newNode_222_, 0);
lean_inc_ref(v_ks_225_);
v_vs_226_ = lean_ctor_get(v_newNode_222_, 1);
lean_inc_ref(v_vs_226_);
lean_dec_ref(v_newNode_222_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_x_166_, v_ks_225_, v_vs_226_, v___x_227_, v___x_228_);
lean_dec_ref(v_vs_226_);
lean_dec_ref(v_ks_225_);
return v___x_229_;
}
else
{
return v_newNode_222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(size_t v_depth_237_, lean_object* v_keys_238_, lean_object* v_vals_239_, lean_object* v_i_240_, lean_object* v_entries_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_keys_238_);
v___x_243_ = lean_nat_dec_lt(v_i_240_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_i_240_);
return v_entries_241_;
}
else
{
lean_object* v_k_244_; lean_object* v_v_245_; uint64_t v___y_247_; 
v_k_244_ = lean_array_fget_borrowed(v_keys_238_, v_i_240_);
v_v_245_ = lean_array_fget_borrowed(v_vals_239_, v_i_240_);
if (lean_obj_tag(v_k_244_) == 0)
{
uint64_t v___x_258_; 
v___x_258_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_247_ = v___x_258_;
goto v___jp_246_;
}
else
{
uint64_t v_hash_259_; 
v_hash_259_ = lean_ctor_get_uint64(v_k_244_, sizeof(void*)*2);
v___y_247_ = v_hash_259_;
goto v___jp_246_;
}
v___jp_246_:
{
size_t v_h_248_; size_t v___x_249_; lean_object* v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v_h_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_h_248_ = lean_uint64_to_usize(v___y_247_);
v___x_249_ = ((size_t)5ULL);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_sub(v_depth_237_, v___x_251_);
v___x_253_ = lean_usize_mul(v___x_249_, v___x_252_);
v_h_254_ = lean_usize_shift_right(v_h_248_, v___x_253_);
v___x_255_ = lean_nat_add(v_i_240_, v___x_250_);
lean_dec(v_i_240_);
lean_inc(v_v_245_);
lean_inc(v_k_244_);
v___x_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_entries_241_, v_h_254_, v_depth_237_, v_k_244_, v_v_245_);
v_i_240_ = v___x_255_;
v_entries_241_ = v___x_256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_260_, lean_object* v_keys_261_, lean_object* v_vals_262_, lean_object* v_i_263_, lean_object* v_entries_264_){
_start:
{
size_t v_depth_boxed_265_; lean_object* v_res_266_; 
v_depth_boxed_265_ = lean_unbox_usize(v_depth_260_);
lean_dec(v_depth_260_);
v_res_266_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_boxed_265_, v_keys_261_, v_vals_262_, v_i_263_, v_entries_264_);
lean_dec_ref(v_vals_262_);
lean_dec_ref(v_keys_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___boxed(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
size_t v_x_2078__boxed_272_; size_t v_x_2079__boxed_273_; lean_object* v_res_274_; 
v_x_2078__boxed_272_ = lean_unbox_usize(v_x_268_);
lean_dec(v_x_268_);
v_x_2079__boxed_273_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_267_, v_x_2078__boxed_272_, v_x_2079__boxed_273_, v_x_270_, v_x_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
uint64_t v___y_279_; 
if (lean_obj_tag(v_x_276_) == 0)
{
uint64_t v___x_283_; 
v___x_283_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_279_ = v___x_283_;
goto v___jp_278_;
}
else
{
uint64_t v_hash_284_; 
v_hash_284_ = lean_ctor_get_uint64(v_x_276_, sizeof(void*)*2);
v___y_279_ = v_hash_284_;
goto v___jp_278_;
}
v___jp_278_:
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_uint64_to_usize(v___y_279_);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_275_, v___x_280_, v___x_281_, v_x_276_, v_x_277_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(lean_object* v_vs_285_, lean_object* v_v_286_, lean_object* v_i_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_array_get_size(v_vs_285_);
v___x_289_ = lean_nat_dec_lt(v_i_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec(v_i_287_);
v___x_290_ = lean_array_push(v_vs_285_, v_v_286_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v_val_293_; uint8_t v___x_294_; 
v_val_291_ = lean_ctor_get(v_v_286_, 1);
v___x_292_ = lean_array_fget_borrowed(v_vs_285_, v_i_287_);
v_val_293_ = lean_ctor_get(v___x_292_, 1);
v___x_294_ = lean_expr_eqv(v_val_291_, v_val_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_i_287_, v___x_295_);
lean_dec(v_i_287_);
v_i_287_ = v___x_296_;
goto _start;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_array_fset(v_vs_285_, v_i_287_, v_v_286_);
lean_dec(v_i_287_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(lean_object* v_vs_299_, lean_object* v_v_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(v_vs_299_, v_v_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v_fst_305_; lean_object* v_fst_306_; uint8_t v___x_307_; 
v_fst_305_ = lean_ctor_get(v_a_303_, 0);
v_fst_306_ = lean_ctor_get(v_b_304_, 0);
v___x_307_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_305_, v_fst_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_a_308_, v_b_309_);
lean_dec_ref(v_b_309_);
lean_dec_ref(v_a_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_312_, lean_object* v_keys_313_, lean_object* v_v_314_, lean_object* v_k_315_, lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_c_319_; lean_object* v___x_320_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_x_312_, v___x_317_);
v_c_319_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_313_, v_v_314_, v___x_318_);
lean_dec(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_k_315_);
lean_ctor_set(v___x_320_, 1, v_c_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_321_, lean_object* v_keys_322_, lean_object* v_v_323_, lean_object* v_k_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_321_, v_keys_322_, v_v_323_, v_k_324_, v_x_325_);
lean_dec_ref(v_keys_322_);
lean_dec(v_x_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(lean_object* v_x_331_, lean_object* v_keys_332_, lean_object* v_v_333_, lean_object* v_k_334_, lean_object* v_as_335_, lean_object* v_k_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_mid_341_; lean_object* v_midVal_342_; uint8_t v___x_343_; 
v___x_339_ = lean_nat_add(v_x_337_, v_x_338_);
v___x_340_ = lean_unsigned_to_nat(1u);
v_mid_341_ = lean_nat_shiftr(v___x_339_, v___x_340_);
lean_dec(v___x_339_);
v_midVal_342_ = lean_array_fget(v_as_335_, v_mid_341_);
v___x_343_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_midVal_342_, v_k_336_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
lean_dec(v_x_338_);
v___x_344_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_336_, v_midVal_342_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
lean_dec(v_x_337_);
v___x_345_ = lean_array_get_size(v_as_335_);
v___x_346_ = lean_nat_dec_lt(v_mid_341_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec(v_midVal_342_);
lean_dec(v_mid_341_);
lean_dec(v_k_334_);
lean_dec_ref(v_v_333_);
return v_as_335_;
}
else
{
lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_359_; 
v_snd_347_ = lean_ctor_get(v_midVal_342_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_midVal_342_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_midVal_342_, 0);
lean_dec(v_unused_360_);
v___x_349_ = v_midVal_342_;
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_dec(v_midVal_342_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v_xs_x27_352_; lean_object* v___x_353_; lean_object* v_c_354_; lean_object* v___x_356_; 
v___x_351_ = lean_box(0);
v_xs_x27_352_ = lean_array_fset(v_as_335_, v_mid_341_, v___x_351_);
v___x_353_ = lean_nat_add(v_x_331_, v___x_340_);
v_c_354_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_332_, v_v_333_, v___x_353_, v_snd_347_);
lean_dec(v___x_353_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_c_354_);
lean_ctor_set(v___x_349_, 0, v_k_334_);
v___x_356_ = v___x_349_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_c_354_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_array_fset(v_xs_x27_352_, v_mid_341_, v___x_356_);
lean_dec(v_mid_341_);
return v___x_357_;
}
}
}
}
else
{
lean_dec(v_midVal_342_);
v_x_338_ = v_mid_341_;
goto _start;
}
}
else
{
uint8_t v___x_362_; 
lean_dec(v_midVal_342_);
v___x_362_ = lean_nat_dec_eq(v_mid_341_, v_x_337_);
if (v___x_362_ == 0)
{
lean_dec(v_x_337_);
v_x_337_ = v_mid_341_;
goto _start;
}
else
{
lean_object* v___x_364_; lean_object* v_c_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_j_368_; lean_object* v_as_369_; lean_object* v___x_370_; 
lean_dec(v_mid_341_);
lean_dec(v_x_338_);
v___x_364_ = lean_nat_add(v_x_331_, v___x_340_);
v_c_365_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_332_, v_v_333_, v___x_364_);
lean_dec(v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_k_334_);
lean_ctor_set(v___x_366_, 1, v_c_365_);
v___x_367_ = lean_nat_add(v_x_337_, v___x_340_);
lean_dec(v_x_337_);
v_j_368_ = lean_array_get_size(v_as_335_);
v_as_369_ = lean_array_push(v_as_335_, v___x_366_);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_367_, v_as_369_, v_j_368_);
lean_dec(v___x_367_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(lean_object* v_x_371_, lean_object* v_keys_372_, lean_object* v_v_373_, lean_object* v_k_374_, lean_object* v_as_375_, lean_object* v_k_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = lean_array_get_size(v_as_375_);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_nat_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_array_fget_borrowed(v_as_375_, v___x_378_);
v___x_381_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_376_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_380_, v_k_376_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_lt(v___x_378_, v___x_377_);
if (v___x_383_ == 0)
{
lean_dec(v_k_374_);
lean_dec_ref(v_v_373_);
return v_as_375_;
}
else
{
lean_object* v___x_384_; lean_object* v_xs_x27_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_inc(v___x_380_);
v___x_384_ = lean_box(0);
v_xs_x27_385_ = lean_array_fset(v_as_375_, v___x_378_, v___x_384_);
v___x_386_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v___x_380_);
v___x_387_ = lean_array_fset(v_xs_x27_385_, v___x_378_, v___x_386_);
return v___x_387_;
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_sub(v___x_377_, v___x_388_);
v___x_390_ = lean_array_fget_borrowed(v_as_375_, v___x_389_);
v___x_391_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_390_, v_k_376_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_376_, v___x_390_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = lean_nat_dec_lt(v___x_389_, v___x_377_);
if (v___x_393_ == 0)
{
lean_dec(v___x_389_);
lean_dec(v_k_374_);
lean_dec_ref(v_v_373_);
return v_as_375_;
}
else
{
lean_object* v___x_394_; lean_object* v_xs_x27_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc(v___x_390_);
v___x_394_ = lean_box(0);
v_xs_x27_395_ = lean_array_fset(v_as_375_, v___x_389_, v___x_394_);
v___x_396_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v___x_390_);
v___x_397_ = lean_array_fset(v_xs_x27_395_, v___x_389_, v___x_396_);
lean_dec(v___x_389_);
return v___x_397_;
}
}
else
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v_as_375_, v_k_376_, v___x_378_, v___x_389_);
return v___x_398_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v___x_389_);
v___x_399_ = lean_box(0);
v___x_400_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v___x_399_);
v___x_401_ = lean_array_push(v_as_375_, v___x_400_);
return v___x_401_;
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_as_404_; lean_object* v___x_405_; 
v___x_402_ = lean_box(0);
v___x_403_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v___x_402_);
v_as_404_ = lean_array_push(v_as_375_, v___x_403_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_378_, v_as_404_, v___x_377_);
return v___x_405_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
v___x_407_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_371_, v_keys_372_, v_v_373_, v_k_374_, v___x_406_);
v___x_408_ = lean_array_push(v_as_375_, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_keys_409_, lean_object* v_v_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_vs_413_; lean_object* v_children_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_431_; 
v_vs_413_ = lean_ctor_get(v_x_412_, 0);
v_children_414_ = lean_ctor_get(v_x_412_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_431_ == 0)
{
v___x_416_ = v_x_412_;
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_children_414_);
lean_inc(v_vs_413_);
lean_dec(v_x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_array_get_size(v_keys_409_);
v___x_419_ = lean_nat_dec_lt(v_x_411_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(v_vs_413_, v_v_410_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_420_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_children_414_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v_k_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_c_427_; lean_object* v___x_429_; 
v_k_424_ = lean_array_fget_borrowed(v_keys_409_, v_x_411_);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1));
lean_inc_n(v_k_424_, 2);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_k_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v_c_427_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_411_, v_keys_409_, v_v_410_, v_k_424_, v_children_414_, v___x_426_);
lean_dec_ref_known(v___x_426_, 2);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_c_427_);
v___x_429_ = v___x_416_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_vs_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_c_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_432_, lean_object* v_keys_433_, lean_object* v_v_434_, lean_object* v_k_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v_snd_437_ = lean_ctor_get(v_x_436_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_x_436_, 0);
lean_dec(v_unused_448_);
v___x_439_ = v_x_436_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v_x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_c_443_; lean_object* v___x_445_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_x_432_, v___x_441_);
v_c_443_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_433_, v_v_434_, v___x_442_, v_snd_437_);
lean_dec(v___x_442_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_c_443_);
lean_ctor_set(v___x_439_, 0, v_k_435_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_k_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_c_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_449_, lean_object* v_keys_450_, lean_object* v_v_451_, lean_object* v_k_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_449_, v_keys_450_, v_v_451_, v_k_452_, v_x_453_);
lean_dec_ref(v_keys_450_);
lean_dec(v_x_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___boxed(lean_object* v_keys_455_, lean_object* v_v_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_455_, v_v_456_, v_x_457_, v_x_458_);
lean_dec(v_x_457_);
lean_dec_ref(v_keys_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_x_460_, lean_object* v_keys_461_, lean_object* v_v_462_, lean_object* v_k_463_, lean_object* v_as_464_, lean_object* v_k_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_460_, v_keys_461_, v_v_462_, v_k_463_, v_as_464_, v_k_465_, v_x_466_, v_x_467_);
lean_dec_ref(v_k_465_);
lean_dec_ref(v_keys_461_);
lean_dec(v_x_460_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___boxed(lean_object* v_x_469_, lean_object* v_keys_470_, lean_object* v_v_471_, lean_object* v_k_472_, lean_object* v_as_473_, lean_object* v_k_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_469_, v_keys_470_, v_v_471_, v_k_472_, v_as_473_, v_k_474_);
lean_dec_ref(v_k_474_);
lean_dec_ref(v_keys_470_);
lean_dec(v_x_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_get_size(v_keys_476_);
v___x_481_ = lean_nat_dec_lt(v_i_478_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v_i_478_);
v___x_482_ = lean_box(0);
return v___x_482_;
}
else
{
lean_object* v_k_x27_483_; uint8_t v___x_484_; 
v_k_x27_483_ = lean_array_fget_borrowed(v_keys_476_, v_i_478_);
v___x_484_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_479_, v_k_x27_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_i_478_, v___x_485_);
lean_dec(v_i_478_);
v_i_478_ = v___x_486_;
goto _start;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_array_fget_borrowed(v_vals_477_, v_i_478_);
lean_dec(v_i_478_);
lean_inc(v___x_488_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_i_492_, lean_object* v_k_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_490_, v_vals_491_, v_i_492_, v_k_493_);
lean_dec(v_k_493_);
lean_dec_ref(v_vals_491_);
lean_dec_ref(v_keys_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_495_, size_t v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_es_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_j_503_; lean_object* v___x_504_; 
v_es_498_ = lean_ctor_get(v_x_495_, 0);
v___x_499_ = lean_box(2);
v___x_500_ = ((size_t)5ULL);
v___x_501_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_502_ = lean_usize_land(v_x_496_, v___x_501_);
v_j_503_ = lean_usize_to_nat(v___x_502_);
v___x_504_ = lean_array_get_borrowed(v___x_499_, v_es_498_, v_j_503_);
lean_dec(v_j_503_);
switch(lean_obj_tag(v___x_504_))
{
case 0:
{
lean_object* v_key_505_; lean_object* v_val_506_; uint8_t v___x_507_; 
v_key_505_ = lean_ctor_get(v___x_504_, 0);
v_val_506_ = lean_ctor_get(v___x_504_, 1);
v___x_507_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_497_, v_key_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; 
lean_inc(v_val_506_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_val_506_);
return v___x_509_;
}
}
case 1:
{
lean_object* v_node_510_; size_t v___x_511_; 
v_node_510_ = lean_ctor_get(v___x_504_, 0);
v___x_511_ = lean_usize_shift_right(v_x_496_, v___x_500_);
v_x_495_ = v_node_510_;
v_x_496_ = v___x_511_;
goto _start;
}
default: 
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
}
else
{
lean_object* v_ks_514_; lean_object* v_vs_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_ks_514_ = lean_ctor_get(v_x_495_, 0);
v_vs_515_ = lean_ctor_get(v_x_495_, 1);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_514_, v_vs_515_, v___x_516_, v_x_497_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_2529__boxed_521_; lean_object* v_res_522_; 
v_x_2529__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_res_522_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_518_, v_x_2529__boxed_521_, v_x_520_);
lean_dec(v_x_520_);
lean_dec_ref(v_x_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint64_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_523_, v___x_526_, v_x_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_528_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_x_528_);
return v_res_530_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(lean_object* v_msg_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0);
v___x_534_ = lean_panic_fn_borrowed(v___x_533_, v_msg_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_564_; 
v_ks_539_ = lean_ctor_get(v_x_535_, 0);
v_vs_540_ = lean_ctor_get(v_x_535_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_564_ == 0)
{
v___x_542_ = v_x_535_;
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_535_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_get_size(v_ks_539_);
v___x_545_ = lean_nat_dec_lt(v_x_536_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
lean_dec(v_x_536_);
v___x_546_ = lean_array_push(v_ks_539_, v_x_537_);
v___x_547_ = lean_array_push(v_vs_540_, v_x_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_547_);
lean_ctor_set(v___x_542_, 0, v___x_546_);
v___x_549_ = v___x_542_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v_k_x27_551_; uint8_t v___x_552_; 
v_k_x27_551_ = lean_array_fget_borrowed(v_ks_539_, v_x_536_);
v___x_552_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_537_, v_k_x27_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_554_; 
if (v_isShared_543_ == 0)
{
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_vs_540_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_x_536_, v___x_555_);
lean_dec(v_x_536_);
v_x_535_ = v___x_554_;
v_x_536_ = v___x_556_;
goto _start;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = lean_array_fset(v_ks_539_, v_x_536_, v_x_537_);
v___x_560_ = lean_array_fset(v_vs_540_, v_x_536_, v_x_538_);
lean_dec(v_x_536_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_560_);
lean_ctor_set(v___x_542_, 0, v___x_559_);
v___x_562_ = v___x_542_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_n_565_, lean_object* v_k_566_, lean_object* v_v_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_n_565_, v___x_568_, v_k_566_, v_v_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_x_571_, size_t v_x_572_, size_t v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_571_) == 0)
{
lean_object* v_es_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v_j_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_es_576_ = lean_ctor_get(v_x_571_, 0);
v___x_577_ = ((size_t)5ULL);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_580_ = lean_usize_land(v_x_572_, v___x_579_);
v_j_581_ = lean_usize_to_nat(v___x_580_);
v___x_582_ = lean_array_get_size(v_es_576_);
v___x_583_ = lean_nat_dec_lt(v_j_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v_j_581_);
lean_dec(v_x_575_);
lean_dec(v_x_574_);
return v_x_571_;
}
else
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_620_; 
lean_inc_ref(v_es_576_);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_571_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_x_571_, 0);
lean_dec(v_unused_621_);
v___x_585_ = v_x_571_;
v_isShared_586_ = v_isSharedCheck_620_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_x_571_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_620_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_v_587_; lean_object* v___x_588_; lean_object* v_xs_x27_589_; lean_object* v___y_591_; 
v_v_587_ = lean_array_fget(v_es_576_, v_j_581_);
v___x_588_ = lean_box(0);
v_xs_x27_589_ = lean_array_fset(v_es_576_, v_j_581_, v___x_588_);
switch(lean_obj_tag(v_v_587_))
{
case 0:
{
lean_object* v_key_596_; lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
v_key_596_ = lean_ctor_get(v_v_587_, 0);
v_val_597_ = lean_ctor_get(v_v_587_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_v_587_);
if (v_isSharedCheck_607_ == 0)
{
v___x_599_ = v_v_587_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_inc(v_key_596_);
lean_dec(v_v_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_574_, v_key_596_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_599_);
v___x_602_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_596_, v_val_597_, v_x_574_, v_x_575_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___y_591_ = v___x_603_;
goto v___jp_590_;
}
else
{
lean_object* v___x_605_; 
lean_dec(v_val_597_);
lean_dec(v_key_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v_x_575_);
lean_ctor_set(v___x_599_, 0, v_x_574_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_x_574_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_x_575_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v___y_591_ = v___x_605_;
goto v___jp_590_;
}
}
}
}
case 1:
{
lean_object* v_node_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_618_; 
v_node_608_ = lean_ctor_get(v_v_587_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_v_587_);
if (v_isSharedCheck_618_ == 0)
{
v___x_610_ = v_v_587_;
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_node_608_);
lean_dec(v_v_587_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_612_ = lean_usize_shift_right(v_x_572_, v___x_577_);
v___x_613_ = lean_usize_add(v_x_573_, v___x_578_);
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_node_608_, v___x_612_, v___x_613_, v_x_574_, v_x_575_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_614_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v___y_591_ = v___x_616_;
goto v___jp_590_;
}
}
}
default: 
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_x_574_);
lean_ctor_set(v___x_619_, 1, v_x_575_);
v___y_591_ = v___x_619_;
goto v___jp_590_;
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_array_fset(v_xs_x27_589_, v_j_581_, v___y_591_);
lean_dec(v_j_581_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_592_);
v___x_594_ = v___x_585_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
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
else
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_643_; 
v_ks_622_ = lean_ctor_get(v_x_571_, 0);
v_vs_623_ = lean_ctor_get(v_x_571_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_571_);
if (v_isSharedCheck_643_ == 0)
{
v___x_625_ = v_x_571_;
v_isShared_626_ = v_isSharedCheck_643_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_vs_623_);
lean_inc(v_ks_622_);
lean_dec(v_x_571_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_643_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_ks_622_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_vs_623_);
v___x_628_ = v_reuseFailAlloc_642_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v_newNode_629_; uint8_t v___y_631_; size_t v___x_637_; uint8_t v___x_638_; 
v_newNode_629_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v___x_628_, v_x_574_, v_x_575_);
v___x_637_ = ((size_t)7ULL);
v___x_638_ = lean_usize_dec_le(v___x_637_, v_x_573_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_629_);
v___x_640_ = lean_unsigned_to_nat(4u);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
lean_dec(v___x_639_);
v___y_631_ = v___x_641_;
goto v___jp_630_;
}
else
{
v___y_631_ = v___x_638_;
goto v___jp_630_;
}
v___jp_630_:
{
if (v___y_631_ == 0)
{
lean_object* v_ks_632_; lean_object* v_vs_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_ks_632_ = lean_ctor_get(v_newNode_629_, 0);
lean_inc_ref(v_ks_632_);
v_vs_633_ = lean_ctor_get(v_newNode_629_, 1);
lean_inc_ref(v_vs_633_);
lean_dec_ref(v_newNode_629_);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_636_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_x_573_, v_ks_632_, v_vs_633_, v___x_634_, v___x_635_);
lean_dec_ref(v_vs_633_);
lean_dec_ref(v_ks_632_);
return v___x_636_;
}
else
{
return v_newNode_629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(size_t v_depth_644_, lean_object* v_keys_645_, lean_object* v_vals_646_, lean_object* v_i_647_, lean_object* v_entries_648_){
_start:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_array_get_size(v_keys_645_);
v___x_650_ = lean_nat_dec_lt(v_i_647_, v___x_649_);
if (v___x_650_ == 0)
{
lean_dec(v_i_647_);
return v_entries_648_;
}
else
{
lean_object* v_k_651_; lean_object* v_v_652_; uint64_t v___x_653_; size_t v_h_654_; size_t v___x_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; size_t v_h_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_k_651_ = lean_array_fget_borrowed(v_keys_645_, v_i_647_);
v_v_652_ = lean_array_fget_borrowed(v_vals_646_, v_i_647_);
v___x_653_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_651_);
v_h_654_ = lean_uint64_to_usize(v___x_653_);
v___x_655_ = ((size_t)5ULL);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_sub(v_depth_644_, v___x_657_);
v___x_659_ = lean_usize_mul(v___x_655_, v___x_658_);
v_h_660_ = lean_usize_shift_right(v_h_654_, v___x_659_);
v___x_661_ = lean_nat_add(v_i_647_, v___x_656_);
lean_dec(v_i_647_);
lean_inc(v_v_652_);
lean_inc(v_k_651_);
v___x_662_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_entries_648_, v_h_660_, v_depth_644_, v_k_651_, v_v_652_);
v_i_647_ = v___x_661_;
v_entries_648_ = v___x_662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_664_, lean_object* v_keys_665_, lean_object* v_vals_666_, lean_object* v_i_667_, lean_object* v_entries_668_){
_start:
{
size_t v_depth_boxed_669_; lean_object* v_res_670_; 
v_depth_boxed_669_ = lean_unbox_usize(v_depth_664_);
lean_dec(v_depth_664_);
v_res_670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_boxed_669_, v_keys_665_, v_vals_666_, v_i_667_, v_entries_668_);
lean_dec_ref(v_vals_666_);
lean_dec_ref(v_keys_665_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
size_t v_x_2679__boxed_676_; size_t v_x_2680__boxed_677_; lean_object* v_res_678_; 
v_x_2679__boxed_676_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_x_2680__boxed_677_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_671_, v_x_2679__boxed_676_, v_x_2680__boxed_677_, v_x_674_, v_x_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
uint64_t v___x_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_682_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_680_);
v___x_683_ = lean_uint64_to_usize(v___x_682_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_679_, v___x_683_, v___x_684_, v_x_680_, v_x_681_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_690_ = lean_unsigned_to_nat(23u);
v___x_691_ = lean_unsigned_to_nat(166u);
v___x_692_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_693_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_694_ = l_mkPanicMessageWithDecl(v___x_693_, v___x_692_, v___x_691_, v___x_690_, v___x_689_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_695_, lean_object* v_keys_696_, lean_object* v_v_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_array_get_size(v_keys_696_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_k_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v_k_702_ = lean_array_get_borrowed(v___x_701_, v_keys_696_, v___x_699_);
v___x_703_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_d_695_, v_k_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_704_; lean_object* v_c_705_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v_c_705_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_696_, v_v_697_, v___x_704_);
lean_inc(v_k_702_);
v___x_706_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_695_, v_k_702_, v_c_705_);
return v___x_706_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v_c_709_; lean_object* v___x_710_; 
v_val_707_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_703_, 1);
v___x_708_ = lean_unsigned_to_nat(1u);
v_c_709_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_696_, v_v_697_, v___x_708_, v_val_707_);
lean_inc(v_k_702_);
v___x_710_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_695_, v_k_702_, v_c_709_);
return v___x_710_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref(v_v_697_);
lean_dec_ref(v_d_695_);
v___x_711_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_712_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_713_, lean_object* v_keys_714_, lean_object* v_v_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_713_, v_keys_714_, v_v_715_);
lean_dec_ref(v_keys_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(lean_object* v_xs_717_, lean_object* v_v_718_, lean_object* v_i_719_){
_start:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_xs_717_);
v___x_721_ = lean_nat_dec_lt(v_i_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v_i_719_);
v___x_722_ = lean_box(0);
return v___x_722_;
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_array_fget_borrowed(v_xs_717_, v_i_719_);
v___x_724_ = lean_name_eq(v___x_723_, v_v_718_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_i_719_, v___x_725_);
lean_dec(v_i_719_);
v_i_719_ = v___x_726_;
goto _start;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_i_719_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21___boxed(lean_object* v_xs_729_, lean_object* v_v_730_, lean_object* v_i_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_729_, v_v_730_, v_i_731_);
lean_dec(v_v_730_);
lean_dec_ref(v_xs_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(lean_object* v_xs_733_, lean_object* v_v_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_733_, v_v_734_, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14___boxed(lean_object* v_xs_737_, lean_object* v_v_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_xs_737_, v_v_738_);
lean_dec(v_v_738_);
lean_dec_ref(v_xs_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(lean_object* v_x_740_, size_t v_x_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
lean_object* v_es_743_; lean_object* v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v_j_748_; lean_object* v_entry_749_; 
v_es_743_ = lean_ctor_get(v_x_740_, 0);
v___x_744_ = lean_box(2);
v___x_745_ = ((size_t)5ULL);
v___x_746_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_747_ = lean_usize_land(v_x_741_, v___x_746_);
v_j_748_ = lean_usize_to_nat(v___x_747_);
v_entry_749_ = lean_array_get(v___x_744_, v_es_743_, v_j_748_);
switch(lean_obj_tag(v_entry_749_))
{
case 0:
{
lean_object* v_key_750_; uint8_t v___x_751_; 
v_key_750_ = lean_ctor_get(v_entry_749_, 0);
lean_inc(v_key_750_);
lean_dec_ref_known(v_entry_749_, 2);
v___x_751_ = lean_name_eq(v_x_742_, v_key_750_);
lean_dec(v_key_750_);
if (v___x_751_ == 0)
{
lean_dec(v_j_748_);
return v_x_740_;
}
else
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_759_; 
lean_inc_ref(v_es_743_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_x_740_, 0);
lean_dec(v_unused_760_);
v___x_753_ = v_x_740_;
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
else
{
lean_dec(v_x_740_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_array_set(v_es_743_, v_j_748_, v___x_744_);
lean_dec(v_j_748_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
case 1:
{
lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_794_; 
lean_inc_ref(v_es_743_);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_x_740_, 0);
lean_dec(v_unused_795_);
v___x_762_ = v_x_740_;
v_isShared_763_ = v_isSharedCheck_794_;
goto v_resetjp_761_;
}
else
{
lean_dec(v_x_740_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_794_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_node_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_793_; 
v_node_764_ = lean_ctor_get(v_entry_749_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_entry_749_);
if (v_isSharedCheck_793_ == 0)
{
v___x_766_ = v_entry_749_;
v_isShared_767_ = v_isSharedCheck_793_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_node_764_);
lean_dec(v_entry_749_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_793_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_entries_768_; size_t v___x_769_; lean_object* v_newNode_770_; lean_object* v___x_771_; 
v_entries_768_ = lean_array_set(v_es_743_, v_j_748_, v___x_744_);
v___x_769_ = lean_usize_shift_right(v_x_741_, v___x_745_);
v_newNode_770_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_node_764_, v___x_769_, v_x_742_);
lean_inc_ref(v_newNode_770_);
v___x_771_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_773_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v_newNode_770_);
v___x_773_ = v___x_766_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_newNode_770_);
v___x_773_ = v_reuseFailAlloc_778_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_array_set(v_entries_768_, v_j_748_, v___x_773_);
lean_dec(v_j_748_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_774_);
v___x_776_ = v___x_762_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_val_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_newNode_770_);
lean_del_object(v___x_766_);
v_val_779_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_771_, 1);
v_fst_780_ = lean_ctor_get(v_val_779_, 0);
v_snd_781_ = lean_ctor_get(v_val_779_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_val_779_);
if (v_isSharedCheck_792_ == 0)
{
v___x_783_ = v_val_779_;
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_val_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_781_);
v___x_786_ = v_reuseFailAlloc_791_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_set(v_entries_768_, v_j_748_, v___x_786_);
lean_dec(v_j_748_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_787_);
v___x_789_ = v___x_762_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_748_);
return v_x_740_;
}
}
}
else
{
lean_object* v_ks_796_; lean_object* v_vs_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_811_; 
v_ks_796_ = lean_ctor_get(v_x_740_, 0);
v_vs_797_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_811_ == 0)
{
v___x_799_ = v_x_740_;
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_vs_797_);
lean_inc(v_ks_796_);
lean_dec(v_x_740_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_ks_796_, v_x_742_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_803_; 
if (v_isShared_800_ == 0)
{
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_ks_796_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_vs_797_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
lean_object* v_val_805_; lean_object* v_keys_x27_806_; lean_object* v_vals_x27_807_; lean_object* v___x_809_; 
v_val_805_ = lean_ctor_get(v___x_801_, 0);
lean_inc_n(v_val_805_, 2);
lean_dec_ref_known(v___x_801_, 1);
v_keys_x27_806_ = l_Array_eraseIdx___redArg(v_ks_796_, v_val_805_);
v_vals_x27_807_ = l_Array_eraseIdx___redArg(v_vs_797_, v_val_805_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_vals_x27_807_);
lean_ctor_set(v___x_799_, 0, v_keys_x27_806_);
v___x_809_ = v___x_799_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_keys_x27_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_vals_x27_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg___boxed(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_2928__boxed_815_; lean_object* v_res_816_; 
v_x_2928__boxed_815_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_res_816_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_812_, v_x_2928__boxed_815_, v_x_814_);
lean_dec(v_x_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint64_t v___y_820_; 
if (lean_obj_tag(v_x_818_) == 0)
{
uint64_t v___x_823_; 
v___x_823_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_820_ = v___x_823_;
goto v___jp_819_;
}
else
{
uint64_t v_hash_824_; 
v_hash_824_ = lean_ctor_get_uint64(v_x_818_, sizeof(void*)*2);
v___y_820_ = v_hash_824_;
goto v___jp_819_;
}
v___jp_819_:
{
size_t v_h_821_; lean_object* v___x_822_; 
v_h_821_ = lean_uint64_to_usize(v___y_820_);
v___x_822_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_817_, v_h_821_, v_x_818_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_825_, v_x_826_);
lean_dec(v_x_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_828_, lean_object* v_e_829_){
_start:
{
lean_object* v_globalName_x3f_830_; 
v_globalName_x3f_830_ = lean_ctor_get(v_e_829_, 3);
if (lean_obj_tag(v_globalName_x3f_830_) == 0)
{
lean_object* v_keys_831_; lean_object* v_discrTree_832_; lean_object* v_instanceNames_833_; lean_object* v_erased_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_keys_831_ = lean_ctor_get(v_e_829_, 0);
lean_inc_ref(v_keys_831_);
v_discrTree_832_ = lean_ctor_get(v_d_828_, 0);
v_instanceNames_833_ = lean_ctor_get(v_d_828_, 1);
v_erased_834_ = lean_ctor_get(v_d_828_, 2);
v_isSharedCheck_842_ = !lean_is_exclusive(v_d_828_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v_d_828_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_erased_834_);
lean_inc(v_instanceNames_833_);
lean_inc(v_discrTree_832_);
lean_dec(v_d_828_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_832_, v_keys_831_, v_e_829_);
lean_dec_ref(v_keys_831_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_instanceNames_833_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_erased_834_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_keys_843_; lean_object* v_val_844_; lean_object* v_discrTree_845_; lean_object* v_instanceNames_846_; lean_object* v_erased_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_857_; 
v_keys_843_ = lean_ctor_get(v_e_829_, 0);
v_val_844_ = lean_ctor_get(v_globalName_x3f_830_, 0);
lean_inc(v_val_844_);
v_discrTree_845_ = lean_ctor_get(v_d_828_, 0);
v_instanceNames_846_ = lean_ctor_get(v_d_828_, 1);
v_erased_847_ = lean_ctor_get(v_d_828_, 2);
v_isSharedCheck_857_ = !lean_is_exclusive(v_d_828_);
if (v_isSharedCheck_857_ == 0)
{
v___x_849_ = v_d_828_;
v_isShared_850_ = v_isSharedCheck_857_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_erased_847_);
lean_inc(v_instanceNames_846_);
lean_inc(v_discrTree_845_);
lean_dec(v_d_828_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_857_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_inc_ref(v_e_829_);
v___x_851_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_845_, v_keys_843_, v_e_829_);
lean_inc(v_val_844_);
v___x_852_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_846_, v_val_844_, v_e_829_);
v___x_853_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_847_, v_val_844_);
lean_dec(v_val_844_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 2, v___x_853_);
lean_ctor_set(v___x_849_, 1, v___x_852_);
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_867_, v_x_868_, v_x_869_);
lean_dec(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec(v_x_877_);
lean_dec_ref(v_x_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_x_880_, v_x_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, size_t v_x_886_, size_t v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_885_, v_x_886_, v_x_887_, v_x_888_, v_x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___boxed(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
size_t v_x_3153__boxed_897_; size_t v_x_3154__boxed_898_; lean_object* v_res_899_; 
v_x_3153__boxed_897_ = lean_unbox_usize(v_x_893_);
lean_dec(v_x_893_);
v_x_3154__boxed_898_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_res_899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(v_00_u03b2_891_, v_x_892_, v_x_3153__boxed_897_, v_x_3154__boxed_898_, v_x_895_, v_x_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(lean_object* v_00_u03b2_900_, lean_object* v_x_901_, size_t v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_901_, v_x_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___boxed(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
size_t v_x_3170__boxed_909_; lean_object* v_res_910_; 
v_x_3170__boxed_909_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_910_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(v_00_u03b2_905_, v_x_906_, v_x_3170__boxed_909_, v_x_908_);
lean_dec(v_x_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, size_t v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
size_t v_x_3181__boxed_920_; lean_object* v_res_921_; 
v_x_3181__boxed_920_ = lean_unbox_usize(v_x_918_);
lean_dec(v_x_918_);
v_res_921_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_00_u03b2_916_, v_x_917_, v_x_3181__boxed_920_, v_x_919_);
lean_dec(v_x_919_);
lean_dec_ref(v_x_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, size_t v_x_924_, size_t v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_923_, v_x_924_, v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
size_t v_x_3192__boxed_935_; size_t v_x_3193__boxed_936_; lean_object* v_res_937_; 
v_x_3192__boxed_935_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_x_3193__boxed_936_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_res_937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(v_00_u03b2_929_, v_x_930_, v_x_3192__boxed_935_, v_x_3193__boxed_936_, v_x_933_, v_x_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_938_, lean_object* v_n_939_, lean_object* v_k_940_, lean_object* v_v_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v_n_939_, v_k_940_, v_v_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_943_, size_t v_depth_944_, lean_object* v_keys_945_, lean_object* v_vals_946_, lean_object* v_heq_947_, lean_object* v_i_948_, lean_object* v_entries_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_944_, v_keys_945_, v_vals_946_, v_i_948_, v_entries_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_951_, lean_object* v_depth_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_heq_955_, lean_object* v_i_956_, lean_object* v_entries_957_){
_start:
{
size_t v_depth_boxed_958_; lean_object* v_res_959_; 
v_depth_boxed_958_ = lean_unbox_usize(v_depth_952_);
lean_dec(v_depth_952_);
v_res_959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(v_00_u03b2_951_, v_depth_boxed_958_, v_keys_953_, v_vals_954_, v_heq_955_, v_i_956_, v_entries_957_);
lean_dec_ref(v_vals_954_);
lean_dec_ref(v_keys_953_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_960_, lean_object* v_keys_961_, lean_object* v_vals_962_, lean_object* v_heq_963_, lean_object* v_i_964_, lean_object* v_k_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_961_, v_vals_962_, v_i_964_, v_k_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_967_, lean_object* v_keys_968_, lean_object* v_vals_969_, lean_object* v_heq_970_, lean_object* v_i_971_, lean_object* v_k_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_967_, v_keys_968_, v_vals_969_, v_heq_970_, v_i_971_, v_k_972_);
lean_dec(v_k_972_);
lean_dec_ref(v_vals_969_);
lean_dec_ref(v_keys_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_974_, lean_object* v_n_975_, lean_object* v_k_976_, lean_object* v_v_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v_n_975_, v_k_976_, v_v_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_979_, size_t v_depth_980_, lean_object* v_keys_981_, lean_object* v_vals_982_, lean_object* v_heq_983_, lean_object* v_i_984_, lean_object* v_entries_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_980_, v_keys_981_, v_vals_982_, v_i_984_, v_entries_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_987_, lean_object* v_depth_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_entries_993_){
_start:
{
size_t v_depth_boxed_994_; lean_object* v_res_995_; 
v_depth_boxed_994_ = lean_unbox_usize(v_depth_988_);
lean_dec(v_depth_988_);
v_res_995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_987_, v_depth_boxed_994_, v_keys_989_, v_vals_990_, v_heq_991_, v_i_992_, v_entries_993_);
lean_dec_ref(v_vals_990_);
lean_dec_ref(v_keys_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(lean_object* v_x_996_, lean_object* v_keys_997_, lean_object* v_v_998_, lean_object* v_k_999_, lean_object* v_as_1000_, lean_object* v_k_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_996_, v_keys_997_, v_v_998_, v_k_999_, v_as_1000_, v_k_1001_, v_x_1002_, v_x_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___boxed(lean_object* v_x_1007_, lean_object* v_keys_1008_, lean_object* v_v_1009_, lean_object* v_k_1010_, lean_object* v_as_1011_, lean_object* v_k_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(v_x_1007_, v_keys_1008_, v_v_1009_, v_k_1010_, v_as_1011_, v_k_1012_, v_x_1013_, v_x_1014_, v_x_1015_, v_x_1016_);
lean_dec_ref(v_k_1012_);
lean_dec_ref(v_keys_1008_);
lean_dec(v_x_1007_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_x_1019_, v_x_1020_, v_x_1021_, v_x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1025_, v_x_1026_, v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1030_, lean_object* v_declName_1031_){
_start:
{
lean_object* v_discrTree_1032_; lean_object* v_instanceNames_1033_; lean_object* v_erased_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v_discrTree_1032_ = lean_ctor_get(v_d_1030_, 0);
v_instanceNames_1033_ = lean_ctor_get(v_d_1030_, 1);
v_erased_1034_ = lean_ctor_get(v_d_1030_, 2);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_d_1030_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1036_ = v_d_1030_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_erased_1034_);
lean_inc(v_instanceNames_1033_);
lean_inc(v_discrTree_1032_);
lean_dec(v_d_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1038_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1033_, v_declName_1031_);
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1034_, v_declName_1031_, v___x_1039_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 2, v___x_1040_);
lean_ctor_set(v___x_1036_, 1, v___x_1038_);
v___x_1042_ = v___x_1036_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_discrTree_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1045_, lean_object* v_declName_1046_, lean_object* v_toPure_1047_, lean_object* v_____r_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = l_Lean_Meta_Instances_eraseCore(v_d_1045_, v_declName_1046_);
v___x_1050_ = lean_apply_2(v_toPure_1047_, lean_box(0), v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1051_, lean_object* v_____r_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_apply_1(v___f_1051_, v_____r_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_d_1064_, lean_object* v_declName_1065_){
_start:
{
lean_object* v_toApplicative_1066_; lean_object* v_toBind_1067_; lean_object* v_toPure_1068_; lean_object* v_instanceNames_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; uint8_t v___x_1073_; 
v_toApplicative_1066_ = lean_ctor_get(v_inst_1062_, 0);
v_toBind_1067_ = lean_ctor_get(v_inst_1062_, 1);
lean_inc(v_toBind_1067_);
v_toPure_1068_ = lean_ctor_get(v_toApplicative_1066_, 1);
v_instanceNames_1069_ = lean_ctor_get(v_d_1064_, 1);
v___x_1070_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1068_);
lean_inc_n(v_declName_1065_, 2);
lean_inc_ref(v_d_1064_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1072_, 0, v_d_1064_);
lean_closure_set(v___f_1072_, 1, v_declName_1065_);
lean_closure_set(v___f_1072_, 2, v_toPure_1068_);
lean_inc_ref(v_instanceNames_1069_);
v___x_1073_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1070_, v___x_1071_, v_instanceNames_1069_, v_declName_1065_);
if (v___x_1073_ == 0)
{
lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v_d_1064_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1074_, 0, v___f_1072_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1076_ = l_Lean_MessageData_ofConstName(v_declName_1065_, v___x_1073_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_throwError___redArg(v_inst_1062_, v_inst_1063_, v___x_1079_);
v___x_1081_ = lean_apply_4(v_toBind_1067_, lean_box(0), lean_box(0), v___x_1080_, v___f_1074_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_inc(v_toPure_1068_);
lean_dec_ref(v___f_1072_);
lean_dec(v_toBind_1067_);
lean_dec_ref(v_inst_1063_);
lean_dec_ref(v_inst_1062_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1064_, v_declName_1065_, v_toPure_1068_, v___x_1082_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_d_1087_, lean_object* v_declName_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1085_, v_inst_1086_, v_d_1087_, v_declName_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v_x_1090_, lean_object* v_e_1091_){
_start:
{
lean_object* v_globalName_x3f_1096_; 
v_globalName_x3f_1096_ = lean_ctor_get(v_e_1091_, 3);
lean_inc(v_globalName_x3f_1096_);
if (lean_obj_tag(v_globalName_x3f_1096_) == 0)
{
goto v___jp_1092_;
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
v_val_1097_ = lean_ctor_get(v_globalName_x3f_1096_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_globalName_x3f_1096_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1099_ = v_globalName_x3f_1096_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_val_1097_);
lean_dec(v_globalName_x3f_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_isPrivateName(v_val_1097_);
lean_dec(v_val_1097_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1103_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_e_1091_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_e_1091_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
lean_inc_ref_n(v___x_1103_, 2);
v___x_1104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
return v___x_1104_;
}
}
else
{
lean_del_object(v___x_1099_);
goto v___jp_1092_;
}
}
}
v___jp_1092_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_e_1091_);
v___x_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1094_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_x_1107_, lean_object* v_e_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v_x_1107_, v_e_1108_);
lean_dec_ref(v_x_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v___y_1110_){
_start:
{
lean_inc_ref(v___y_1110_);
return v___y_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v___y_1111_);
lean_dec_ref(v___y_1111_);
return v_res_1112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___f_1121_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___f_1122_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1123_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1124_);
lean_ctor_set(v___x_1126_, 2, v___x_1123_);
lean_ctor_set(v___x_1126_, 3, v___f_1122_);
lean_ctor_set(v___x_1126_, 4, v___f_1121_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_);
v___x_1129_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1132_, uint8_t v_allowLevelAssignments_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1133_, v_k_1132_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1156_, lean_object* v_allowLevelAssignments_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1163_; lean_object* v_res_1164_; 
v_allowLevelAssignments_boxed_1163_ = lean_unbox(v_allowLevelAssignments_1157_);
v_res_1164_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1156_, v_allowLevelAssignments_boxed_1163_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1165_, lean_object* v_k_1166_, uint8_t v_allowLevelAssignments_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1166_, v_allowLevelAssignments_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_k_1175_, lean_object* v_allowLevelAssignments_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1182_; lean_object* v_res_1183_; 
v_allowLevelAssignments_boxed_1182_ = lean_unbox(v_allowLevelAssignments_1176_);
v_res_1183_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1174_, v_k_1175_, v_allowLevelAssignments_boxed_1182_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1184_, lean_object* v___x_1185_, uint8_t v___x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1184_, v___x_1185_, v___x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v_snd_1194_; lean_object* v_snd_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v_snd_1194_ = lean_ctor_get(v_a_1193_, 1);
lean_inc(v_snd_1194_);
lean_dec(v_a_1193_);
v_snd_1195_ = lean_ctor_get(v_snd_1194_, 1);
lean_inc(v_snd_1195_);
lean_dec(v_snd_1194_);
v___x_1196_ = 0;
v___x_1197_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1195_, v___x_1196_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1197_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1192_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1192_);
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
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_497__boxed_1214_; lean_object* v_res_1215_; 
v___x_497__boxed_1214_ = lean_unbox(v___x_1208_);
v_res_1215_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1206_, v___x_1207_, v___x_497__boxed_1214_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; 
lean_inc(v_a_1220_);
lean_inc_ref(v_a_1219_);
lean_inc(v_a_1218_);
lean_inc_ref(v_a_1217_);
v___x_1222_ = lean_infer_type(v_e_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___f_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = lean_box(0);
v___x_1225_ = 0;
v___x_1226_ = lean_box(v___x_1225_);
v___f_1227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1227_, 0, v_a_1223_);
lean_closure_set(v___f_1227_, 1, v___x_1224_);
lean_closure_set(v___f_1227_, 2, v___x_1226_);
v___x_1228_ = 0;
v___x_1229_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1227_, v___x_1228_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1229_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1230_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1222_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1222_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
v___x_1253_ = lean_apply_7(v_k_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, lean_box(0));
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1254_, lean_object* v_b_1255_, lean_object* v_c_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1254_, v_b_1255_, v_c_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1263_, lean_object* v_k_1264_, uint8_t v_cleanupAnnotations_1265_, uint8_t v_whnfType_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___f_1272_; lean_object* v___x_1273_; 
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1272_, 0, v_k_1264_);
v___x_1273_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1263_, v___f_1272_, v_cleanupAnnotations_1265_, v_whnfType_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1290_, lean_object* v_k_1291_, lean_object* v_cleanupAnnotations_1292_, lean_object* v_whnfType_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1299_; uint8_t v_whnfType_boxed_1300_; lean_object* v_res_1301_; 
v_cleanupAnnotations_boxed_1299_ = lean_unbox(v_cleanupAnnotations_1292_);
v_whnfType_boxed_1300_ = lean_unbox(v_whnfType_1293_);
v_res_1301_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1290_, v_k_1291_, v_cleanupAnnotations_boxed_1299_, v_whnfType_boxed_1300_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1302_, lean_object* v_type_1303_, lean_object* v_k_1304_, uint8_t v_cleanupAnnotations_1305_, uint8_t v_whnfType_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1303_, v_k_1304_, v_cleanupAnnotations_1305_, v_whnfType_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_type_1314_, lean_object* v_k_1315_, lean_object* v_cleanupAnnotations_1316_, lean_object* v_whnfType_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1323_; uint8_t v_whnfType_boxed_1324_; lean_object* v_res_1325_; 
v_cleanupAnnotations_boxed_1323_ = lean_unbox(v_cleanupAnnotations_1316_);
v_whnfType_boxed_1324_ = lean_unbox(v_whnfType_1317_);
v_res_1325_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1313_, v_type_1314_, v_k_1315_, v_cleanupAnnotations_boxed_1323_, v_whnfType_boxed_1324_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1332_);
return v___x_1339_;
}
else
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1393_; 
v_fst_1340_ = lean_ctor_get(v_b_1332_, 0);
v_snd_1341_ = lean_ctor_get(v_b_1332_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_b_1332_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1343_ = v_b_1332_;
v_isShared_1344_ = v_isSharedCheck_1393_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_b_1332_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1393_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_next_1350_; 
v_next_1350_ = lean_ctor_get(v_snd_1341_, 0);
lean_inc(v_next_1350_);
if (lean_obj_tag(v_next_1350_) == 0)
{
goto v___jp_1345_;
}
else
{
lean_object* v_upperBound_1351_; lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1392_; 
v_upperBound_1351_ = lean_ctor_get(v_snd_1341_, 1);
v_val_1352_ = lean_ctor_get(v_next_1350_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_next_1350_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1354_ = v_next_1350_;
v_isShared_1355_ = v_isSharedCheck_1392_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v_next_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1392_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_nat_dec_lt(v_val_1352_, v_upperBound_1351_);
if (v___x_1356_ == 0)
{
lean_del_object(v___x_1354_);
lean_dec(v_val_1352_);
goto v___jp_1345_;
}
else
{
lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1389_; 
lean_inc(v_upperBound_1351_);
lean_del_object(v___x_1343_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_snd_1341_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1390_ = lean_ctor_get(v_snd_1341_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_snd_1341_, 0);
lean_dec(v_unused_1391_);
v___x_1358_ = v_snd_1341_;
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
else
{
lean_dec(v_snd_1341_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v_a_1360_);
v___x_1361_ = lean_infer_type(v_a_1360_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_a_1364_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_val_1352_, v___x_1368_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1369_);
v___x_1371_ = v___x_1354_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1370_;
}
v___jp_1363_:
{
size_t v___x_1365_; size_t v___x_1366_; 
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_add(v_i_1331_, v___x_1365_);
v_i_1331_ = v___x_1366_;
v_b_1332_ = v_a_1364_;
goto _start;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1371_);
v___x_1373_ = v___x_1358_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_upperBound_1351_);
v___x_1373_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1375_ = l_Lean_Expr_isAppOf(v_a_1362_, v___x_1374_);
lean_dec(v_a_1362_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v_val_1352_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_fst_1340_);
lean_ctor_set(v___x_1376_, 1, v___x_1373_);
v_a_1364_ = v___x_1376_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_array_push(v_fst_1340_, v_val_1352_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___x_1373_);
v_a_1364_ = v___x_1378_;
goto v___jp_1363_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_del_object(v___x_1358_);
lean_del_object(v___x_1354_);
lean_dec(v_val_1352_);
lean_dec(v_upperBound_1351_);
lean_dec(v_fst_1340_);
v_a_1381_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1361_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1361_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1347_; 
if (v_isShared_1344_ == 0)
{
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_fst_1340_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1341_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1394_, lean_object* v_sz_1395_, lean_object* v_i_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1395_);
lean_dec(v_sz_1395_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1394_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v_as_1394_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1410_, lean_object* v_args_1411_, lean_object* v_x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v___y_1420_; lean_object* v_env_1445_; lean_object* v___x_1446_; 
v___x_1418_ = lean_st_ref_get(v___y_1416_);
v_env_1445_ = lean_ctor_get(v___x_1418_, 0);
lean_inc_ref(v_env_1445_);
lean_dec(v___x_1418_);
v___x_1446_ = l_Lean_getOutParamPositions_x3f(v_env_1445_, v_declName_1410_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1420_ = v___x_1447_;
goto v___jp_1419_;
}
else
{
lean_object* v_val_1448_; 
v_val_1448_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1448_);
lean_dec_ref_known(v___x_1446_, 1);
v___y_1420_ = v_val_1448_;
goto v___jp_1419_;
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1421_ = lean_array_get_size(v_args_1411_);
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v_sz_1425_ = lean_array_size(v_args_1411_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1411_, v_sz_1425_, v___x_1426_, v___x_1424_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v___x_1434_; 
v_fst_1432_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_fst_1432_);
lean_dec(v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_fst_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_fst_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1427_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1427_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1449_, lean_object* v_args_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1449_, v_args_1450_, v_x_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v_x_1451_);
lean_dec_ref(v_args_1450_);
lean_dec(v_declName_1449_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Expr_getAppFn(v_classTy_1458_);
if (lean_obj_tag(v___x_1464_) == 4)
{
lean_object* v_declName_1465_; lean_object* v___x_1466_; 
v_declName_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_declName_1465_);
lean_inc(v_a_1462_);
lean_inc_ref(v_a_1461_);
lean_inc(v_a_1460_);
lean_inc_ref(v_a_1459_);
v___x_1466_ = lean_infer_type(v___x_1464_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___f_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___f_1468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1468_, 0, v_declName_1465_);
v___x_1469_ = 0;
v___x_1470_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1467_, v___f_1468_, v___x_1469_, v___x_1469_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_declName_1465_);
v_a_1471_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1466_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1466_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v___x_1464_);
v___x_1479_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec_ref(v_classTy_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1488_, lean_object* v_as_1489_, lean_object* v_j_1490_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_array_get_size(v_as_1489_);
v___x_1492_ = lean_nat_dec_lt(v_j_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec(v_j_1490_);
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_array_fget_borrowed(v_as_1489_, v_j_1490_);
v___x_1495_ = l_Lean_Expr_mvarId_x21(v___x_1494_);
v___x_1496_ = l_Lean_instBEqMVarId_beq(v___x_1495_, v_a_1488_);
lean_dec(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1498_ = lean_nat_add(v_j_1490_, v___x_1497_);
lean_dec(v_j_1490_);
v_j_1490_ = v___x_1498_;
goto _start;
}
else
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_j_1490_);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1501_, lean_object* v_as_1502_, lean_object* v_j_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1501_, v_as_1502_, v_j_1503_);
lean_dec_ref(v_as_1502_);
lean_dec(v_a_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v_ks_1509_; lean_object* v_vs_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1534_; 
v_ks_1509_ = lean_ctor_get(v_x_1505_, 0);
v_vs_1510_ = lean_ctor_get(v_x_1505_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1512_ = v_x_1505_;
v_isShared_1513_ = v_isSharedCheck_1534_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_vs_1510_);
lean_inc(v_ks_1509_);
lean_dec(v_x_1505_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1534_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v_ks_1509_);
v___x_1515_ = lean_nat_dec_lt(v_x_1506_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_dec(v_x_1506_);
v___x_1516_ = lean_array_push(v_ks_1509_, v_x_1507_);
v___x_1517_ = lean_array_push(v_vs_1510_, v_x_1508_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v___x_1517_);
lean_ctor_set(v___x_1512_, 0, v___x_1516_);
v___x_1519_ = v___x_1512_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
else
{
lean_object* v_k_x27_1521_; uint8_t v___x_1522_; 
v_k_x27_1521_ = lean_array_fget_borrowed(v_ks_1509_, v_x_1506_);
v___x_1522_ = l_Lean_instBEqMVarId_beq(v_x_1507_, v_k_x27_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1524_; 
if (v_isShared_1513_ == 0)
{
v___x_1524_ = v___x_1512_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_ks_1509_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_vs_1510_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_x_1506_, v___x_1525_);
lean_dec(v_x_1506_);
v_x_1505_ = v___x_1524_;
v_x_1506_ = v___x_1526_;
goto _start;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = lean_array_fset(v_ks_1509_, v_x_1506_, v_x_1507_);
v___x_1530_ = lean_array_fset(v_vs_1510_, v_x_1506_, v_x_1508_);
lean_dec(v_x_1506_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v___x_1530_);
lean_ctor_set(v___x_1512_, 0, v___x_1529_);
v___x_1532_ = v___x_1512_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1530_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1535_, lean_object* v_k_1536_, lean_object* v_v_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1535_, v___x_1538_, v_k_1536_, v_v_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1540_, size_t v_x_1541_, size_t v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_es_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v_j_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_es_1545_ = lean_ctor_get(v_x_1540_, 0);
v___x_1546_ = ((size_t)5ULL);
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_1549_ = lean_usize_land(v_x_1541_, v___x_1548_);
v_j_1550_ = lean_usize_to_nat(v___x_1549_);
v___x_1551_ = lean_array_get_size(v_es_1545_);
v___x_1552_ = lean_nat_dec_lt(v_j_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v_j_1550_);
lean_dec(v_x_1544_);
lean_dec(v_x_1543_);
return v_x_1540_;
}
else
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1589_; 
lean_inc_ref(v_es_1545_);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_x_1540_, 0);
lean_dec(v_unused_1590_);
v___x_1554_ = v_x_1540_;
v_isShared_1555_ = v_isSharedCheck_1589_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_x_1540_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1589_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_v_1556_; lean_object* v___x_1557_; lean_object* v_xs_x27_1558_; lean_object* v___y_1560_; 
v_v_1556_ = lean_array_fget(v_es_1545_, v_j_1550_);
v___x_1557_ = lean_box(0);
v_xs_x27_1558_ = lean_array_fset(v_es_1545_, v_j_1550_, v___x_1557_);
switch(lean_obj_tag(v_v_1556_))
{
case 0:
{
lean_object* v_key_1565_; lean_object* v_val_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1576_; 
v_key_1565_ = lean_ctor_get(v_v_1556_, 0);
v_val_1566_ = lean_ctor_get(v_v_1556_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_v_1556_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1568_ = v_v_1556_;
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_val_1566_);
lean_inc(v_key_1565_);
lean_dec(v_v_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Lean_instBEqMVarId_beq(v_x_1543_, v_key_1565_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1568_);
v___x_1571_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1565_, v_val_1566_, v_x_1543_, v_x_1544_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
v___y_1560_ = v___x_1572_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v_val_1566_);
lean_dec(v_key_1565_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_x_1544_);
lean_ctor_set(v___x_1568_, 0, v_x_1543_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_x_1543_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_x_1544_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
v___y_1560_ = v___x_1574_;
goto v___jp_1559_;
}
}
}
}
case 1:
{
lean_object* v_node_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1587_; 
v_node_1577_ = lean_ctor_get(v_v_1556_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_v_1556_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1579_ = v_v_1556_;
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_node_1577_);
lean_dec(v_v_1556_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
size_t v___x_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1581_ = lean_usize_shift_right(v_x_1541_, v___x_1546_);
v___x_1582_ = lean_usize_add(v_x_1542_, v___x_1547_);
v___x_1583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1577_, v___x_1581_, v___x_1582_, v_x_1543_, v_x_1544_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1585_ = v___x_1579_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
v___y_1560_ = v___x_1585_;
goto v___jp_1559_;
}
}
}
default: 
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_x_1543_);
lean_ctor_set(v___x_1588_, 1, v_x_1544_);
v___y_1560_ = v___x_1588_;
goto v___jp_1559_;
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_array_fset(v_xs_x27_1558_, v_j_1550_, v___y_1560_);
lean_dec(v_j_1550_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1561_);
v___x_1563_ = v___x_1554_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_ks_1591_; lean_object* v_vs_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1612_; 
v_ks_1591_ = lean_ctor_get(v_x_1540_, 0);
v_vs_1592_ = lean_ctor_get(v_x_1540_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1594_ = v_x_1540_;
v_isShared_1595_ = v_isSharedCheck_1612_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_vs_1592_);
lean_inc(v_ks_1591_);
lean_dec(v_x_1540_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1612_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_ks_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_vs_1592_);
v___x_1597_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v_newNode_1598_; uint8_t v___y_1600_; size_t v___x_1606_; uint8_t v___x_1607_; 
v_newNode_1598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1597_, v_x_1543_, v_x_1544_);
v___x_1606_ = ((size_t)7ULL);
v___x_1607_ = lean_usize_dec_le(v___x_1606_, v_x_1542_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1598_);
v___x_1609_ = lean_unsigned_to_nat(4u);
v___x_1610_ = lean_nat_dec_lt(v___x_1608_, v___x_1609_);
lean_dec(v___x_1608_);
v___y_1600_ = v___x_1610_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1607_;
goto v___jp_1599_;
}
v___jp_1599_:
{
if (v___y_1600_ == 0)
{
lean_object* v_ks_1601_; lean_object* v_vs_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_ks_1601_ = lean_ctor_get(v_newNode_1598_, 0);
lean_inc_ref(v_ks_1601_);
v_vs_1602_ = lean_ctor_get(v_newNode_1598_, 1);
lean_inc_ref(v_vs_1602_);
lean_dec_ref(v_newNode_1598_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_1605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1542_, v_ks_1601_, v_vs_1602_, v___x_1603_, v___x_1604_);
lean_dec_ref(v_vs_1602_);
lean_dec_ref(v_ks_1601_);
return v___x_1605_;
}
else
{
return v_newNode_1598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1613_, lean_object* v_keys_1614_, lean_object* v_vals_1615_, lean_object* v_i_1616_, lean_object* v_entries_1617_){
_start:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_array_get_size(v_keys_1614_);
v___x_1619_ = lean_nat_dec_lt(v_i_1616_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v_i_1616_);
return v_entries_1617_;
}
else
{
lean_object* v_k_1620_; lean_object* v_v_1621_; uint64_t v___x_1622_; size_t v_h_1623_; size_t v___x_1624_; lean_object* v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v_h_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_k_1620_ = lean_array_fget_borrowed(v_keys_1614_, v_i_1616_);
v_v_1621_ = lean_array_fget_borrowed(v_vals_1615_, v_i_1616_);
v___x_1622_ = l_Lean_instHashableMVarId_hash(v_k_1620_);
v_h_1623_ = lean_uint64_to_usize(v___x_1622_);
v___x_1624_ = ((size_t)5ULL);
v___x_1625_ = lean_unsigned_to_nat(1u);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_sub(v_depth_1613_, v___x_1626_);
v___x_1628_ = lean_usize_mul(v___x_1624_, v___x_1627_);
v_h_1629_ = lean_usize_shift_right(v_h_1623_, v___x_1628_);
v___x_1630_ = lean_nat_add(v_i_1616_, v___x_1625_);
lean_dec(v_i_1616_);
lean_inc(v_v_1621_);
lean_inc(v_k_1620_);
v___x_1631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1617_, v_h_1629_, v_depth_1613_, v_k_1620_, v_v_1621_);
v_i_1616_ = v___x_1630_;
v_entries_1617_ = v___x_1631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1633_, lean_object* v_keys_1634_, lean_object* v_vals_1635_, lean_object* v_i_1636_, lean_object* v_entries_1637_){
_start:
{
size_t v_depth_boxed_1638_; lean_object* v_res_1639_; 
v_depth_boxed_1638_ = lean_unbox_usize(v_depth_1633_);
lean_dec(v_depth_1633_);
v_res_1639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1638_, v_keys_1634_, v_vals_1635_, v_i_1636_, v_entries_1637_);
lean_dec_ref(v_vals_1635_);
lean_dec_ref(v_keys_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
size_t v_x_1628__boxed_1645_; size_t v_x_1629__boxed_1646_; lean_object* v_res_1647_; 
v_x_1628__boxed_1645_ = lean_unbox_usize(v_x_1641_);
lean_dec(v_x_1641_);
v_x_1629__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_res_1647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1640_, v_x_1628__boxed_1645_, v_x_1629__boxed_1646_, v_x_1643_, v_x_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
uint64_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = l_Lean_instHashableMVarId_hash(v_x_1649_);
v___x_1652_ = lean_uint64_to_usize(v___x_1651_);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1648_, v___x_1652_, v___x_1653_, v_x_1649_, v_x_1650_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1655_, lean_object* v_val_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v_mctx_1660_; lean_object* v_cache_1661_; lean_object* v_zetaDeltaFVarIds_1662_; lean_object* v_postponed_1663_; lean_object* v_diag_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1692_; 
v___x_1659_ = lean_st_ref_take(v___y_1657_);
v_mctx_1660_ = lean_ctor_get(v___x_1659_, 0);
v_cache_1661_ = lean_ctor_get(v___x_1659_, 1);
v_zetaDeltaFVarIds_1662_ = lean_ctor_get(v___x_1659_, 2);
v_postponed_1663_ = lean_ctor_get(v___x_1659_, 3);
v_diag_1664_ = lean_ctor_get(v___x_1659_, 4);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1666_ = v___x_1659_;
v_isShared_1667_ = v_isSharedCheck_1692_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_diag_1664_);
lean_inc(v_postponed_1663_);
lean_inc(v_zetaDeltaFVarIds_1662_);
lean_inc(v_cache_1661_);
lean_inc(v_mctx_1660_);
lean_dec(v___x_1659_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1692_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_depth_1668_; lean_object* v_levelAssignDepth_1669_; lean_object* v_lmvarCounter_1670_; lean_object* v_mvarCounter_1671_; lean_object* v_lDecls_1672_; lean_object* v_decls_1673_; lean_object* v_userNames_1674_; lean_object* v_lAssignment_1675_; lean_object* v_eAssignment_1676_; lean_object* v_dAssignment_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1691_; 
v_depth_1668_ = lean_ctor_get(v_mctx_1660_, 0);
v_levelAssignDepth_1669_ = lean_ctor_get(v_mctx_1660_, 1);
v_lmvarCounter_1670_ = lean_ctor_get(v_mctx_1660_, 2);
v_mvarCounter_1671_ = lean_ctor_get(v_mctx_1660_, 3);
v_lDecls_1672_ = lean_ctor_get(v_mctx_1660_, 4);
v_decls_1673_ = lean_ctor_get(v_mctx_1660_, 5);
v_userNames_1674_ = lean_ctor_get(v_mctx_1660_, 6);
v_lAssignment_1675_ = lean_ctor_get(v_mctx_1660_, 7);
v_eAssignment_1676_ = lean_ctor_get(v_mctx_1660_, 8);
v_dAssignment_1677_ = lean_ctor_get(v_mctx_1660_, 9);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_mctx_1660_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1679_ = v_mctx_1660_;
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_dAssignment_1677_);
lean_inc(v_eAssignment_1676_);
lean_inc(v_lAssignment_1675_);
lean_inc(v_userNames_1674_);
lean_inc(v_decls_1673_);
lean_inc(v_lDecls_1672_);
lean_inc(v_mvarCounter_1671_);
lean_inc(v_lmvarCounter_1670_);
lean_inc(v_levelAssignDepth_1669_);
lean_inc(v_depth_1668_);
lean_dec(v_mctx_1660_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1676_, v_mvarId_1655_, v_val_1656_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 8, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_depth_1668_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_levelAssignDepth_1669_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_lmvarCounter_1670_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_mvarCounter_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_lDecls_1672_);
lean_ctor_set(v_reuseFailAlloc_1690_, 5, v_decls_1673_);
lean_ctor_set(v_reuseFailAlloc_1690_, 6, v_userNames_1674_);
lean_ctor_set(v_reuseFailAlloc_1690_, 7, v_lAssignment_1675_);
lean_ctor_set(v_reuseFailAlloc_1690_, 8, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 9, v_dAssignment_1677_);
v___x_1683_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1683_);
v___x_1685_ = v___x_1666_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_cache_1661_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_zetaDeltaFVarIds_1662_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_postponed_1663_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_diag_1664_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_st_ref_set(v___y_1657_, v___x_1685_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1693_, lean_object* v_val_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1693_, v_val_1694_, v___y_1695_);
lean_dec(v___y_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1698_, lean_object* v_argVars_1699_, lean_object* v_as_1700_, size_t v_sz_1701_, size_t v_i_1702_, lean_object* v_b_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1702_, v_sz_1701_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_b_1703_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; lean_object* v_a_1712_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1711_ = lean_box(0);
v_a_1712_ = lean_array_uget_borrowed(v_as_1700_, v_i_1702_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1712_, v_argMVars_1698_, v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_val_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = l_Lean_instInhabitedExpr;
v___x_1737_ = lean_array_get_borrowed(v___x_1736_, v_argVars_1699_, v_val_1735_);
lean_dec(v_val_1735_);
lean_inc(v___x_1737_);
lean_inc(v_a_1712_);
v___x_1738_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1712_, v___x_1737_, v___y_1705_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
v___y_1714_ = v___y_1704_;
v___y_1715_ = v___y_1705_;
v___y_1716_ = v___y_1706_;
v___y_1717_ = v___y_1707_;
goto v___jp_1713_;
}
else
{
return v___x_1738_;
}
}
else
{
lean_dec(v___x_1734_);
v___y_1714_ = v___y_1704_;
v___y_1715_ = v___y_1705_;
v___y_1716_ = v___y_1706_;
v___y_1717_ = v___y_1707_;
goto v___jp_1713_;
}
v___jp_1713_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc(v_a_1712_);
v___x_1718_ = l_Lean_Expr_mvar___override(v_a_1712_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v___y_1715_);
lean_inc_ref(v___y_1714_);
v___x_1719_ = lean_infer_type(v___x_1718_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1698_, v_argVars_1699_, v_a_1720_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1721_) == 0)
{
size_t v___x_1722_; size_t v___x_1723_; 
lean_dec_ref_known(v___x_1721_, 1);
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1702_, v___x_1722_);
v_i_1702_ = v___x_1723_;
v_b_1703_ = v___x_1711_;
goto _start;
}
else
{
return v___x_1721_;
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1719_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1719_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1739_, lean_object* v_argVars_1740_, lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_getMVars(v_e_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; size_t v_sz_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_box(0);
v_sz_1750_ = lean_array_size(v_a_1748_);
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1739_, v_argVars_1740_, v_a_1748_, v_sz_1750_, v___x_1751_, v___x_1749_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1748_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1752_, 0);
lean_dec(v_unused_1760_);
v___x_1754_ = v___x_1752_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v___x_1752_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1749_);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1749_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
return v___x_1752_;
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1747_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1747_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
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
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1769_, lean_object* v_argVars_1770_, lean_object* v_e_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1769_, v_argVars_1770_, v_e_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec_ref(v_argVars_1770_);
lean_dec_ref(v_argMVars_1769_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1778_, lean_object* v_argVars_1779_, lean_object* v_as_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1778_, v_argVars_1779_, v_as_1780_, v_sz_boxed_1789_, v_i_boxed_1790_, v_b_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v_as_1780_);
lean_dec_ref(v_argVars_1779_);
lean_dec_ref(v_argMVars_1778_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1792_, lean_object* v_val_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1792_, v_val_1793_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1800_, lean_object* v_val_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1800_, v_val_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1809_, v_x_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, size_t v_x_1815_, size_t v_x_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1814_, v_x_1815_, v_x_1816_, v_x_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
size_t v_x_1991__boxed_1826_; size_t v_x_1992__boxed_1827_; lean_object* v_res_1828_; 
v_x_1991__boxed_1826_ = lean_unbox_usize(v_x_1822_);
lean_dec(v_x_1822_);
v_x_1992__boxed_1827_ = lean_unbox_usize(v_x_1823_);
lean_dec(v_x_1823_);
v_res_1828_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1820_, v_x_1821_, v_x_1991__boxed_1826_, v_x_1992__boxed_1827_, v_x_1824_, v_x_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1829_, lean_object* v_n_1830_, lean_object* v_k_1831_, lean_object* v_v_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1830_, v_k_1831_, v_v_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1834_, size_t v_depth_1835_, lean_object* v_keys_1836_, lean_object* v_vals_1837_, lean_object* v_heq_1838_, lean_object* v_i_1839_, lean_object* v_entries_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1835_, v_keys_1836_, v_vals_1837_, v_i_1839_, v_entries_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1842_, lean_object* v_depth_1843_, lean_object* v_keys_1844_, lean_object* v_vals_1845_, lean_object* v_heq_1846_, lean_object* v_i_1847_, lean_object* v_entries_1848_){
_start:
{
size_t v_depth_boxed_1849_; lean_object* v_res_1850_; 
v_depth_boxed_1849_ = lean_unbox_usize(v_depth_1843_);
lean_dec(v_depth_1843_);
v_res_1850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1842_, v_depth_boxed_1849_, v_keys_1844_, v_vals_1845_, v_heq_1846_, v_i_1847_, v_entries_1848_);
lean_dec_ref(v_vals_1845_);
lean_dec_ref(v_keys_1844_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1852_, v_x_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_hasMVar(v_e_1857_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_e_1857_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v_mctx_1863_; lean_object* v___x_1864_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v_cache_1868_; lean_object* v_zetaDeltaFVarIds_1869_; lean_object* v_postponed_1870_; lean_object* v_diag_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
v___x_1862_ = lean_st_ref_get(v___y_1858_);
v_mctx_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_mctx_1863_);
lean_dec(v___x_1862_);
v___x_1864_ = l_Lean_instantiateMVarsCore(v_mctx_1863_, v_e_1857_);
v_fst_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_fst_1865_);
v_snd_1866_ = lean_ctor_get(v___x_1864_, 1);
lean_inc(v_snd_1866_);
lean_dec_ref(v___x_1864_);
v___x_1867_ = lean_st_ref_take(v___y_1858_);
v_cache_1868_ = lean_ctor_get(v___x_1867_, 1);
v_zetaDeltaFVarIds_1869_ = lean_ctor_get(v___x_1867_, 2);
v_postponed_1870_ = lean_ctor_get(v___x_1867_, 3);
v_diag_1871_ = lean_ctor_get(v___x_1867_, 4);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1881_);
v___x_1873_ = v___x_1867_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_diag_1871_);
lean_inc(v_postponed_1870_);
lean_inc(v_zetaDeltaFVarIds_1869_);
lean_inc(v_cache_1868_);
lean_dec(v___x_1867_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_snd_1866_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_snd_1866_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_zetaDeltaFVarIds_1869_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_postponed_1870_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_diag_1871_);
v___x_1876_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_st_ref_set(v___y_1858_, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_fst_1865_);
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1882_, v___y_1883_);
lean_dec(v___y_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1886_, v___y_1888_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1900_, lean_object* v_opt_1901_){
_start:
{
lean_object* v_name_1902_; lean_object* v_defValue_1903_; lean_object* v_map_1904_; lean_object* v___x_1905_; 
v_name_1902_ = lean_ctor_get(v_opt_1901_, 0);
v_defValue_1903_ = lean_ctor_get(v_opt_1901_, 1);
v_map_1904_ = lean_ctor_get(v_opts_1900_, 0);
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1904_, v_name_1902_);
if (lean_obj_tag(v___x_1905_) == 0)
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_unbox(v_defValue_1903_);
return v___x_1906_;
}
else
{
lean_object* v_val_1907_; 
v_val_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v___x_1905_, 1);
if (lean_obj_tag(v_val_1907_) == 1)
{
uint8_t v_v_1908_; 
v_v_1908_ = lean_ctor_get_uint8(v_val_1907_, 0);
lean_dec_ref_known(v_val_1907_, 0);
return v_v_1908_;
}
else
{
uint8_t v___x_1909_; 
lean_dec(v_val_1907_);
v___x_1909_ = lean_unbox(v_defValue_1903_);
return v___x_1909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1910_, lean_object* v_opt_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1910_, v_opt_1911_);
lean_dec_ref(v_opt_1911_);
lean_dec_ref(v_opts_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1914_, lean_object* v_as_1915_, size_t v_i_1916_, size_t v_stop_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_eq(v_i_1916_, v_stop_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = lean_array_uget_borrowed(v_as_1915_, v_i_1916_);
v___x_1920_ = lean_nat_dec_eq(v_a_1914_, v___x_1919_);
if (v___x_1920_ == 0)
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1916_, v___x_1921_);
v_i_1916_ = v___x_1922_;
goto _start;
}
else
{
return v___x_1920_;
}
}
else
{
uint8_t v___x_1924_; 
v___x_1924_ = 0;
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_stop_1928_){
_start:
{
size_t v_i_boxed_1929_; size_t v_stop_boxed_1930_; uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_i_boxed_1929_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_stop_boxed_1930_ = lean_unbox_usize(v_stop_1928_);
lean_dec(v_stop_1928_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1925_, v_as_1926_, v_i_boxed_1929_, v_stop_boxed_1930_);
lean_dec_ref(v_as_1926_);
lean_dec(v_a_1925_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_array_get_size(v_as_1933_);
v___x_1937_ = lean_nat_dec_lt(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1936_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1934_, v_as_1933_, v___x_1938_, v___x_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1941_, lean_object* v_a_1942_){
_start:
{
uint8_t v_res_1943_; lean_object* v_r_1944_; 
v_res_1943_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_as_1941_);
v_r_1944_ = lean_box(v_res_1943_);
return v_r_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1945_, lean_object* v_fst_1946_, lean_object* v_argVars_1947_, lean_object* v_as_1948_, size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_a_1958_; uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_b_1951_);
return v___x_1963_;
}
else
{
lean_object* v_next_1964_; 
v_next_1964_ = lean_ctor_get(v_b_1951_, 0);
lean_inc(v_next_1964_);
if (lean_obj_tag(v_next_1964_) == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1951_);
return v___x_1965_;
}
else
{
lean_object* v_upperBound_1966_; lean_object* v_val_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1998_; 
v_upperBound_1966_ = lean_ctor_get(v_b_1951_, 1);
v_val_1967_ = lean_ctor_get(v_next_1964_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_next_1964_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1969_ = v_next_1964_;
v_isShared_1970_ = v_isSharedCheck_1998_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_val_1967_);
lean_dec(v_next_1964_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1998_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_nat_dec_lt(v_val_1967_, v_upperBound_1966_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
lean_del_object(v___x_1969_);
lean_dec(v_val_1967_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_b_1951_);
return v___x_1972_;
}
else
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1995_; 
lean_inc(v_upperBound_1966_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_b_1951_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1996_ = lean_ctor_get(v_b_1951_, 1);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_b_1951_, 0);
lean_dec(v_unused_1997_);
v___x_1974_ = v_b_1951_;
v_isShared_1975_ = v_isSharedCheck_1995_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v_b_1951_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1995_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_add(v_val_1967_, v___x_1976_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1977_);
v___x_1979_ = v___x_1969_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1979_);
v___x_1981_ = v___x_1974_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_upperBound_1966_);
v___x_1981_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1945_, v_val_1967_);
lean_dec(v_val_1967_);
if (v___x_1982_ == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1984_; 
v_a_1983_ = lean_array_uget_borrowed(v_as_1948_, v_i_1950_);
lean_inc(v_a_1983_);
v___x_1984_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1946_, v_argVars_1947_, v_a_1983_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_dec_ref_known(v___x_1984_, 1);
v_a_1958_ = v___x_1981_;
goto v___jp_1957_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v___x_1981_);
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
v_a_1958_ = v___x_1981_;
goto v___jp_1957_;
}
}
}
}
}
}
}
}
v___jp_1957_:
{
size_t v___x_1959_; size_t v___x_1960_; 
v___x_1959_ = ((size_t)1ULL);
v___x_1960_ = lean_usize_add(v_i_1950_, v___x_1959_);
v_i_1950_ = v___x_1960_;
v_b_1951_ = v_a_1958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_1999_, lean_object* v_fst_2000_, lean_object* v_argVars_2001_, lean_object* v_as_2002_, lean_object* v_sz_2003_, lean_object* v_i_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
size_t v_sz_boxed_2011_; size_t v_i_boxed_2012_; lean_object* v_res_2013_; 
v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2003_);
lean_dec(v_sz_2003_);
v_i_boxed_2012_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_1999_, v_fst_2000_, v_argVars_2001_, v_as_2002_, v_sz_boxed_2011_, v_i_boxed_2012_, v_b_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v_as_2002_);
lean_dec_ref(v_argVars_2001_);
lean_dec_ref(v_fst_2000_);
lean_dec_ref(v_a_1999_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
if (lean_obj_tag(v_a_2015_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_List_reverse___redArg(v_a_2016_);
return v___x_2017_;
}
else
{
lean_object* v_head_2018_; lean_object* v_tail_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2034_; 
v_head_2018_ = lean_ctor_get(v_a_2015_, 0);
v_tail_2019_ = lean_ctor_get(v_a_2015_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2021_ = v_a_2015_;
v_isShared_2022_ = v_isSharedCheck_2034_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_tail_2019_);
lean_inc(v_head_2018_);
lean_dec(v_a_2015_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2034_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2023_ = 0;
v___x_2024_ = lean_box(v___x_2023_);
v___x_2025_ = lean_array_get(v___x_2024_, v_fst_2014_, v_head_2018_);
lean_dec(v___x_2024_);
v___x_2026_ = 3;
v___x_2027_ = lean_unbox(v___x_2025_);
lean_dec(v___x_2025_);
v___x_2028_ = l_Lean_instBEqBinderInfo_beq(v___x_2027_, v___x_2026_);
if (v___x_2028_ == 0)
{
lean_del_object(v___x_2021_);
lean_dec(v_head_2018_);
v_a_2015_ = v_tail_2019_;
goto _start;
}
else
{
lean_object* v___x_2031_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v_a_2016_);
v___x_2031_ = v___x_2021_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_head_2018_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_a_2016_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v_a_2015_ = v_tail_2019_;
v_a_2016_ = v___x_2031_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2035_, v_a_2036_, v_a_2037_);
lean_dec_ref(v_fst_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; lean_object* v_env_2046_; lean_object* v___x_2047_; lean_object* v_mctx_2048_; lean_object* v_lctx_2049_; lean_object* v_options_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2045_ = lean_st_ref_get(v___y_2043_);
v_env_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_st_ref_get(v___y_2041_);
v_mctx_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_ref(v_mctx_2048_);
lean_dec(v___x_2047_);
v_lctx_2049_ = lean_ctor_get(v___y_2040_, 2);
v_options_2050_ = lean_ctor_get(v___y_2042_, 2);
lean_inc_ref(v_options_2050_);
lean_inc_ref(v_lctx_2049_);
v___x_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2051_, 0, v_env_2046_);
lean_ctor_set(v___x_2051_, 1, v_mctx_2048_);
lean_ctor_set(v___x_2051_, 2, v_lctx_2049_);
lean_ctor_set(v___x_2051_, 3, v_options_2050_);
v___x_2052_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_msgData_2039_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_ref_2067_; lean_object* v___x_2068_; lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2077_; 
v_ref_2067_ = lean_ctor_get(v___y_2064_, 5);
v___x_2068_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_inc(v_ref_2067_);
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_ref_2067_);
lean_ctor_set(v___x_2073_, 1, v_a_2069_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 1);
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2085_, size_t v_sz_2086_, size_t v_i_2087_, lean_object* v_bs_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2087_, v_sz_2086_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_bs_2088_);
return v___x_2095_;
}
else
{
lean_object* v_v_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_v_2096_ = lean_array_uget_borrowed(v_bs_2088_, v_i_2087_);
v___x_2097_ = l_Lean_instInhabitedExpr;
v___x_2098_ = lean_array_get_borrowed(v___x_2097_, v_argVars_2085_, v_v_2096_);
lean_inc(v___y_2092_);
lean_inc_ref(v___y_2091_);
lean_inc(v___y_2090_);
lean_inc_ref(v___y_2089_);
lean_inc(v___x_2098_);
v___x_2099_ = lean_infer_type(v___x_2098_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v_bs_x27_2102_; lean_object* v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = lean_unsigned_to_nat(0u);
v_bs_x27_2102_ = lean_array_uset(v_bs_2088_, v_i_2087_, v___x_2101_);
v___x_2103_ = l_Lean_indentExpr(v_a_2100_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2087_, v___x_2104_);
v___x_2106_ = lean_array_uset(v_bs_x27_2102_, v_i_2087_, v___x_2103_);
v_i_2087_ = v___x_2105_;
v_bs_2088_ = v___x_2106_;
goto _start;
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_bs_2088_);
v_a_2108_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2099_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2099_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2116_, lean_object* v_sz_2117_, lean_object* v_i_2118_, lean_object* v_bs_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2117_);
lean_dec(v_sz_2117_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2116_, v_sz_boxed_2125_, v_i_boxed_2126_, v_bs_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_argVars_2116_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
if (lean_obj_tag(v_a_2128_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_List_reverse___redArg(v_a_2129_);
return v___x_2130_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2143_; 
v_head_2131_ = lean_ctor_get(v_a_2128_, 0);
v_tail_2132_ = lean_ctor_get(v_a_2128_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2134_ = v_a_2128_;
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_tail_2132_);
lean_inc(v_head_2131_);
lean_dec(v_a_2128_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2136_ = l_Nat_reprFast(v_head_2131_);
v___x_2137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
v___x_2138_ = l_Lean_MessageData_ofFormat(v___x_2137_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 1, v_a_2129_);
lean_ctor_set(v___x_2134_, 0, v___x_2138_);
v___x_2140_ = v___x_2134_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2129_);
v___x_2140_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
v_a_2128_ = v_tail_2132_;
v_a_2129_ = v___x_2140_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2144_, lean_object* v___x_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_b_2148_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_nat_dec_lt(v_a_2147_, v_upperBound_2144_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v_a_2147_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_b_2148_);
return v___x_2151_;
}
else
{
lean_object* v_snd_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2193_; 
v_snd_2152_ = lean_ctor_get(v_b_2148_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_b_2148_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v_b_2148_, 0);
lean_dec(v_unused_2194_);
v___x_2154_ = v_b_2148_;
v_isShared_2155_ = v_isSharedCheck_2193_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_snd_2152_);
lean_dec(v_b_2148_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2193_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_array_2156_; lean_object* v_start_2157_; lean_object* v_stop_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_array_2156_ = lean_ctor_get(v_snd_2152_, 0);
v_start_2157_ = lean_ctor_get(v_snd_2152_, 1);
v_stop_2158_ = lean_ctor_get(v_snd_2152_, 2);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_nat_dec_lt(v_start_2157_, v_stop_2158_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2162_; 
lean_dec(v_a_2147_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2159_);
v___x_2162_ = v___x_2154_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_snd_2152_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
else
{
lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2189_; 
lean_inc(v_stop_2158_);
lean_inc(v_start_2157_);
lean_inc_ref(v_array_2156_);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_snd_2152_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; 
v_unused_2190_ = lean_ctor_get(v_snd_2152_, 2);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_snd_2152_, 1);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_snd_2152_, 0);
lean_dec(v_unused_2192_);
v___x_2166_ = v_snd_2152_;
v_isShared_2167_ = v_isSharedCheck_2189_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v_snd_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2189_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = lean_nat_dec_eq(v___x_2145_, v___x_2168_);
v___x_2170_ = lean_array_fget(v_array_2156_, v_start_2157_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_start_2157_, v___x_2171_);
lean_dec(v_start_2157_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v___x_2172_);
v___x_2174_ = v___x_2166_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_array_2156_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_stop_2158_);
v___x_2174_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
uint8_t v___x_2187_; 
v___x_2187_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2146_, v_a_2147_);
if (v___x_2187_ == 0)
{
goto v___jp_2181_;
}
else
{
if (v___x_2169_ == 0)
{
lean_dec(v___x_2170_);
goto v___jp_2175_;
}
else
{
goto v___jp_2181_;
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2174_);
lean_ctor_set(v___x_2154_, 0, v___x_2159_);
v___x_2177_ = v___x_2154_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2174_);
v___x_2177_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_nat_add(v_a_2147_, v___x_2171_);
lean_dec(v_a_2147_);
v_a_2147_ = v___x_2178_;
v_b_2148_ = v___x_2177_;
goto _start;
}
}
v___jp_2181_:
{
uint8_t v___x_2182_; 
v___x_2182_ = l_Lean_Expr_hasExprMVar(v___x_2170_);
lean_dec(v___x_2170_);
if (v___x_2182_ == 0)
{
goto v___jp_2175_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_del_object(v___x_2154_);
lean_dec(v_a_2147_);
v___x_2183_ = lean_box(v___x_2169_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2174_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2195_, lean_object* v___x_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2195_, v___x_2196_, v_a_2197_, v_a_2198_, v_b_2199_);
lean_dec_ref(v_a_2197_);
lean_dec(v___x_2196_);
lean_dec(v_upperBound_2195_);
return v_res_2201_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2202_; lean_object* v_dummy_2203_; 
v___x_2202_ = lean_box(0);
v_dummy_2203_ = l_Lean_Expr_sort___override(v___x_2202_);
return v_dummy_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2204_, lean_object* v___x_2205_, uint8_t v___x_2206_, lean_object* v_x_2207_, lean_object* v_argTy_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
v___x_2214_ = lean_whnf(v_argTy_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2215_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_dummy_2218_; lean_object* v_nargs_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_dummy_2218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2219_ = l_Lean_Expr_getAppNumArgs(v_a_2215_);
lean_inc(v_nargs_2219_);
v___x_2220_ = lean_mk_array(v_nargs_2219_, v_dummy_2218_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_sub(v_nargs_2219_, v___x_2221_);
lean_dec(v_nargs_2219_);
v___x_2223_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2215_, v___x_2220_, v___x_2222_);
v___x_2224_ = lean_array_get_size(v___x_2223_);
lean_inc(v___x_2204_);
v___x_2225_ = l_Array_toSubarray___redArg(v___x_2223_, v___x_2204_, v___x_2224_);
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2225_);
v___x_2228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2224_, v___x_2205_, v_a_2217_, v___x_2204_, v___x_2227_);
lean_dec(v_a_2217_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2242_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_fst_2233_; 
v_fst_2233_ = lean_ctor_get(v_a_2229_, 0);
lean_inc(v_fst_2233_);
lean_dec(v_a_2229_);
if (lean_obj_tag(v_fst_2233_) == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(v___x_2206_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_val_2238_; lean_object* v___x_2240_; 
v_val_2238_ = lean_ctor_get(v_fst_2233_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_fst_2233_, 1);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_val_2238_);
v___x_2240_ = v___x_2231_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_val_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2228_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2228_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2215_);
lean_dec(v___x_2204_);
v_a_2251_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2216_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2216_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v___x_2204_);
v_a_2259_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2214_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2214_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v___x_2269_, lean_object* v_x_2270_, lean_object* v_argTy_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v___x_26265__boxed_2277_; lean_object* v_res_2278_; 
v___x_26265__boxed_2277_ = lean_unbox(v___x_2269_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2267_, v___x_2268_, v___x_26265__boxed_2277_, v_x_2270_, v_argTy_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_x_2270_);
lean_dec(v___x_2268_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2282_, lean_object* v_projInfo_x3f_2283_, lean_object* v___x_2284_, lean_object* v_argVars_2285_, lean_object* v_as_2286_, size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_lt(v_i_2288_, v_sz_2287_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v___x_2284_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_b_2289_);
return v___x_2296_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_b_2289_);
v_a_2297_ = lean_array_uget_borrowed(v_as_2286_, v_i_2288_);
v___x_2298_ = l_Lean_instInhabitedExpr;
v___x_2299_ = lean_array_get_borrowed(v___x_2298_, v_fst_2282_, v_a_2297_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
lean_inc(v___x_2299_);
v___x_2300_ = lean_infer_type(v___x_2299_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2301_, v___y_2291_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2349_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2349_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2349_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2315_; lean_object* v___y_2317_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___f_2333_; uint8_t v___x_2334_; 
v___x_2307_ = lean_box(0);
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_box(v___x_2295_);
lean_inc(v___x_2284_);
v___f_2333_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2333_, 0, v___x_2331_);
lean_closure_set(v___f_2333_, 1, v___x_2284_);
lean_closure_set(v___f_2333_, 2, v___x_2332_);
v___x_2334_ = lean_nat_dec_eq(v___x_2284_, v___x_2331_);
if (lean_obj_tag(v_projInfo_x3f_2283_) == 1)
{
lean_object* v_val_2335_; lean_object* v_numParams_2336_; uint8_t v___x_2337_; 
v_val_2335_ = lean_ctor_get(v_projInfo_x3f_2283_, 0);
v_numParams_2336_ = lean_ctor_get(v_val_2335_, 1);
v___x_2337_ = lean_nat_dec_eq(v_numParams_2336_, v_a_2297_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2303_, v___f_2333_, v___x_2334_, v___x_2334_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
v___y_2317_ = v___x_2338_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2339_; 
lean_dec_ref(v___f_2333_);
lean_dec(v___x_2284_);
v___x_2339_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2282_, v_argVars_2285_, v_a_2303_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_dec_ref_known(v___x_2339_, 1);
goto v___jp_2308_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_del_object(v___x_2305_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
else
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2303_, v___f_2333_, v___x_2334_, v___x_2334_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
v___y_2317_ = v___x_2348_;
goto v___jp_2316_;
}
v___jp_2308_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_inc(v_a_2297_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2297_);
v___x_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___x_2307_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2311_);
v___x_2313_ = v___x_2305_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
v___jp_2316_:
{
if (lean_obj_tag(v___y_2317_) == 0)
{
lean_object* v_a_2318_; uint8_t v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___y_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___y_2317_, 1);
v___x_2319_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
if (v___x_2319_ == 0)
{
size_t v___x_2320_; size_t v___x_2321_; 
lean_del_object(v___x_2305_);
v___x_2320_ = ((size_t)1ULL);
v___x_2321_ = lean_usize_add(v_i_2288_, v___x_2320_);
v_i_2288_ = v___x_2321_;
v_b_2289_ = v___x_2315_;
goto _start;
}
else
{
lean_dec(v___x_2284_);
goto v___jp_2308_;
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_del_object(v___x_2305_);
lean_dec(v___x_2284_);
v_a_2323_ = lean_ctor_get(v___y_2317_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___y_2317_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___y_2317_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___y_2317_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v___x_2284_);
v_a_2350_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2302_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2302_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v___x_2284_);
v_a_2358_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2300_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2300_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2366_, lean_object* v_projInfo_x3f_2367_, lean_object* v___x_2368_, lean_object* v_argVars_2369_, lean_object* v_as_2370_, lean_object* v_sz_2371_, lean_object* v_i_2372_, lean_object* v_b_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
size_t v_sz_boxed_2379_; size_t v_i_boxed_2380_; lean_object* v_res_2381_; 
v_sz_boxed_2379_ = lean_unbox_usize(v_sz_2371_);
lean_dec(v_sz_2371_);
v_i_boxed_2380_ = lean_unbox_usize(v_i_2372_);
lean_dec(v_i_2372_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2366_, v_projInfo_x3f_2367_, v___x_2368_, v_argVars_2369_, v_as_2370_, v_sz_boxed_2379_, v_i_boxed_2380_, v_b_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_as_2370_);
lean_dec_ref(v_argVars_2369_);
lean_dec(v_projInfo_x3f_2367_);
lean_dec_ref(v_fst_2366_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2382_, size_t v_sz_2383_, size_t v_i_2384_, lean_object* v_bs_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_bs_2385_);
return v___x_2392_;
}
else
{
lean_object* v_v_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_v_2393_ = lean_array_uget_borrowed(v_bs_2385_, v_i_2384_);
v___x_2394_ = l_Lean_instInhabitedExpr;
v___x_2395_ = lean_array_get_borrowed(v___x_2394_, v_fst_2382_, v_v_2393_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___x_2395_);
v___x_2396_ = lean_infer_type(v___x_2395_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2397_, v___y_2387_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v_bs_x27_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = lean_unsigned_to_nat(0u);
v_bs_x27_2401_ = lean_array_uset(v_bs_2385_, v_i_2384_, v___x_2400_);
v___x_2402_ = l_Lean_Expr_setPPExplicit(v_a_2399_, v___x_2391_);
v___x_2403_ = l_Lean_indentExpr(v___x_2402_);
v___x_2404_ = ((size_t)1ULL);
v___x_2405_ = lean_usize_add(v_i_2384_, v___x_2404_);
v___x_2406_ = lean_array_uset(v_bs_x27_2401_, v_i_2384_, v___x_2403_);
v_i_2384_ = v___x_2405_;
v_bs_2385_ = v___x_2406_;
goto _start;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v_bs_2385_);
v_a_2408_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2398_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2398_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v_bs_2385_);
v_a_2416_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2396_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2396_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2424_, lean_object* v_sz_2425_, lean_object* v_i_2426_, lean_object* v_bs_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2425_);
lean_dec(v_sz_2425_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2426_);
lean_dec(v_i_2426_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2424_, v_sz_boxed_2433_, v_i_boxed_2434_, v_bs_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_fst_2424_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v_snd_2436_, lean_object* v___f_2437_, lean_object* v_____r_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = lean_array_get_borrowed(v___x_2444_, v_snd_2436_, v___x_2444_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___x_2445_);
v___x_2446_ = lean_apply_6(v___f_2437_, v___x_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, lean_box(0));
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v_snd_2447_, lean_object* v___f_2448_, lean_object* v_____r_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2447_, v___f_2448_, v_____r_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_snd_2447_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2456_, lean_object* v_as_2457_, size_t v_i_2458_, size_t v_stop_2459_, lean_object* v_b_2460_){
_start:
{
lean_object* v___y_2462_; uint8_t v___x_2466_; 
v___x_2466_ = lean_usize_dec_eq(v_i_2458_, v_stop_2459_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = lean_array_uget_borrowed(v_as_2457_, v_i_2458_);
v___x_2468_ = lean_nat_dec_eq(v___x_2467_, v_next_2456_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_inc(v___x_2467_);
v___x_2469_ = lean_array_push(v_b_2460_, v___x_2467_);
v___y_2462_ = v___x_2469_;
goto v___jp_2461_;
}
else
{
v___y_2462_ = v_b_2460_;
goto v___jp_2461_;
}
}
else
{
return v_b_2460_;
}
v___jp_2461_:
{
size_t v___x_2463_; size_t v___x_2464_; 
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2458_, v___x_2463_);
v_i_2458_ = v___x_2464_;
v_b_2460_ = v___y_2462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2470_, lean_object* v_as_2471_, lean_object* v_i_2472_, lean_object* v_stop_2473_, lean_object* v_b_2474_){
_start:
{
size_t v_i_boxed_2475_; size_t v_stop_boxed_2476_; lean_object* v_res_2477_; 
v_i_boxed_2475_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_stop_boxed_2476_ = lean_unbox_usize(v_stop_2473_);
lean_dec(v_stop_2473_);
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2470_, v_as_2471_, v_i_boxed_2475_, v_stop_boxed_2476_, v_b_2474_);
lean_dec_ref(v_as_2471_);
lean_dec(v_next_2470_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2478_, lean_object* v_fst_2479_, lean_object* v_argVars_2480_, lean_object* v_snd_2481_, lean_object* v_next_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
lean_inc(v_next_2482_);
v___x_2488_ = lean_array_push(v_fst_2478_, v_next_2482_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_get_size(v_snd_2481_);
v___x_2533_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2534_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
if (v___x_2534_ == 0)
{
v___y_2490_ = v___x_2533_;
goto v___jp_2489_;
}
else
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_nat_dec_le(v___x_2532_, v___x_2532_);
if (v___x_2535_ == 0)
{
if (v___x_2534_ == 0)
{
v___y_2490_ = v___x_2533_;
goto v___jp_2489_;
}
else
{
size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2532_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2482_, v_snd_2481_, v___x_2536_, v___x_2537_, v___x_2533_);
v___y_2490_ = v___x_2538_;
goto v___jp_2489_;
}
}
else
{
size_t v___x_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = lean_usize_of_nat(v___x_2532_);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2482_, v_snd_2481_, v___x_2539_, v___x_2540_, v___x_2533_);
v___y_2490_ = v___x_2541_;
goto v___jp_2489_;
}
}
v___jp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = l_Lean_instInhabitedExpr;
v___x_2492_ = lean_array_get_borrowed(v___x_2491_, v_fst_2479_, v_next_2482_);
lean_dec(v_next_2482_);
lean_inc(v___y_2486_);
lean_inc_ref(v___y_2485_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___x_2492_);
v___x_2493_ = lean_infer_type(v___x_2492_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2479_, v_argVars_2480_, v_a_2494_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2495_, 1);
lean_inc(v___x_2492_);
v___x_2496_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2479_, v_argVars_2480_, v___x_2492_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2505_; 
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2496_, 0);
lean_dec(v_unused_2506_);
v___x_2498_ = v___x_2496_;
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v___x_2496_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2488_);
lean_ctor_set(v___x_2500_, 1, v___y_2490_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2501_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___x_2488_);
v_a_2507_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2496_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2496_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___x_2488_);
v_a_2515_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2495_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2495_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___x_2488_);
v_a_2523_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2493_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2493_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2542_, lean_object* v_fst_2543_, lean_object* v_argVars_2544_, lean_object* v_snd_2545_, lean_object* v_next_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2542_, v_fst_2543_, v_argVars_2544_, v_snd_2545_, v_next_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v_snd_2545_);
lean_dec_ref(v_argVars_2544_);
lean_dec_ref(v_fst_2543_);
return v_res_2552_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2557_ = l_Lean_MessageData_ofFormat(v___x_2556_);
return v___x_2557_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
return v___x_2560_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2563_ = l_Lean_stringToMessageData(v___x_2562_);
return v___x_2563_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2566_ = l_Lean_stringToMessageData(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2567_, lean_object* v_argVars_2568_, lean_object* v_inst_2569_, lean_object* v_a_2570_, lean_object* v_projInfo_x3f_2571_, lean_object* v_a_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___y_2579_; lean_object* v_fst_2599_; lean_object* v_snd_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2676_; 
v_fst_2599_ = lean_ctor_get(v_a_2572_, 0);
v_snd_2600_ = lean_ctor_get(v_a_2572_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_a_2572_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2602_ = v_a_2572_;
v_isShared_2603_ = v_isSharedCheck_2676_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_snd_2600_);
lean_inc(v_fst_2599_);
lean_dec(v_a_2572_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2676_;
goto v_resetjp_2601_;
}
v___jp_2578_:
{
if (lean_obj_tag(v___y_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2590_; 
v_a_2580_ = lean_ctor_get(v___y_2579_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___y_2579_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2582_ = v___y_2579_;
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___y_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2590_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
if (lean_obj_tag(v_a_2580_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; 
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
v_a_2584_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v_a_2580_, 1);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v_a_2584_);
v___x_2586_ = v___x_2582_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v_a_2588_; 
lean_del_object(v___x_2582_);
v_a_2588_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v_a_2580_, 1);
v_a_2572_ = v_a_2588_;
goto _start;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
v_a_2591_ = lean_ctor_get(v___y_2579_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___y_2579_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___y_2579_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___y_2579_);
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
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2604_ = lean_array_get_size(v_snd_2600_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; size_t v_sz_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
lean_del_object(v___x_2602_);
v___x_2607_ = lean_box(0);
v___x_2608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2609_ = lean_array_size(v_snd_2600_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2567_, v_projInfo_x3f_2571_, v___x_2604_, v_argVars_2568_, v_snd_2600_, v_sz_2609_, v___x_2610_, v___x_2608_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_fst_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2662_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_fst_2613_ = lean_ctor_get(v_a_2612_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v_a_2612_, 1);
lean_dec(v_unused_2663_);
v___x_2615_ = v_a_2612_;
v_isShared_2616_ = v_isSharedCheck_2662_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_fst_2613_);
lean_dec(v_a_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2662_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___f_2617_; 
lean_inc(v_snd_2600_);
lean_inc_ref(v_argVars_2568_);
lean_inc_ref(v_fst_2567_);
lean_inc(v_fst_2599_);
v___f_2617_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2617_, 0, v_fst_2599_);
lean_closure_set(v___f_2617_, 1, v_fst_2567_);
lean_closure_set(v___f_2617_, 2, v_argVars_2568_);
lean_closure_set(v___f_2617_, 3, v_snd_2600_);
if (lean_obj_tag(v_fst_2613_) == 0)
{
lean_dec(v_fst_2599_);
goto v___jp_2618_;
}
else
{
lean_object* v_val_2659_; 
v_val_2659_ = lean_ctor_get(v_fst_2613_, 0);
lean_inc(v_val_2659_);
lean_dec_ref_known(v_fst_2613_, 1);
if (lean_obj_tag(v_val_2659_) == 0)
{
lean_dec(v_fst_2599_);
goto v___jp_2618_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___f_2617_);
lean_del_object(v___x_2615_);
v_val_2660_ = lean_ctor_get(v_val_2659_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v_val_2659_, 1);
v___x_2661_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2599_, v_fst_2567_, v_argVars_2568_, v_snd_2600_, v_val_2660_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v_snd_2600_);
v___y_2579_ = v___x_2661_;
goto v___jp_2578_;
}
}
v___jp_2618_:
{
lean_object* v_options_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_options_2619_ = lean_ctor_get(v___y_2575_, 2);
v___x_2620_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2621_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_del_object(v___x_2615_);
v___x_2622_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2600_, v___f_2617_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v_snd_2600_);
v___y_2579_ = v___x_2622_;
goto v___jp_2578_;
}
else
{
lean_object* v___x_2623_; 
lean_inc(v_snd_2600_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2567_, v_sz_2609_, v___x_2610_, v_snd_2600_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = lean_array_to_list(v_a_2624_);
v___x_2626_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2627_ = l_Lean_MessageData_joinSep(v___x_2625_, v___x_2626_);
v___x_2628_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2569_);
v___x_2629_ = l_Lean_MessageData_ofExpr(v_inst_2569_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set_tag(v___x_2615_, 7);
lean_ctor_set(v___x_2615_, 1, v___x_2629_);
lean_ctor_set(v___x_2615_, 0, v___x_2628_);
v___x_2631_ = v___x_2615_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2632_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
lean_inc_ref(v_a_2570_);
v___x_2634_ = l_Lean_indentExpr(v_a_2570_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2627_);
v___x_2639_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2638_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2641_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2600_, v___f_2617_, v_a_2640_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v_snd_2600_);
v___y_2579_ = v___x_2641_;
goto v___jp_2578_;
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec_ref(v___f_2617_);
lean_dec(v_snd_2600_);
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
v_a_2642_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2639_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2639_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v___f_2617_);
lean_del_object(v___x_2615_);
lean_dec(v_snd_2600_);
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
v_a_2651_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2623_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2623_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_snd_2600_);
lean_dec(v_fst_2599_);
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
v_a_2664_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2611_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2611_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v___x_2673_; 
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_inst_2569_);
lean_dec_ref(v_argVars_2568_);
lean_dec_ref(v_fst_2567_);
if (v_isShared_2603_ == 0)
{
v___x_2673_ = v___x_2602_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_fst_2599_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_snd_2600_);
v___x_2673_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2677_, lean_object* v_argVars_2678_, lean_object* v_inst_2679_, lean_object* v_a_2680_, lean_object* v_projInfo_x3f_2681_, lean_object* v_a_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2677_, v_argVars_2678_, v_inst_2679_, v_a_2680_, v_projInfo_x3f_2681_, v_a_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v_projInfo_x3f_2681_);
return v_res_2688_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2689_; double v___x_2690_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_float_of_nat(v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_ref_2700_; lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2746_; 
v_ref_2700_ = lean_ctor_get(v___y_2697_, 5);
v___x_2701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2746_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2746_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v_traceState_2707_; lean_object* v_env_2708_; lean_object* v_nextMacroScope_2709_; lean_object* v_ngen_2710_; lean_object* v_auxDeclNGen_2711_; lean_object* v_cache_2712_; lean_object* v_messages_2713_; lean_object* v_infoState_2714_; lean_object* v_snapshotTasks_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2745_; 
v___x_2706_ = lean_st_ref_take(v___y_2698_);
v_traceState_2707_ = lean_ctor_get(v___x_2706_, 4);
v_env_2708_ = lean_ctor_get(v___x_2706_, 0);
v_nextMacroScope_2709_ = lean_ctor_get(v___x_2706_, 1);
v_ngen_2710_ = lean_ctor_get(v___x_2706_, 2);
v_auxDeclNGen_2711_ = lean_ctor_get(v___x_2706_, 3);
v_cache_2712_ = lean_ctor_get(v___x_2706_, 5);
v_messages_2713_ = lean_ctor_get(v___x_2706_, 6);
v_infoState_2714_ = lean_ctor_get(v___x_2706_, 7);
v_snapshotTasks_2715_ = lean_ctor_get(v___x_2706_, 8);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2717_ = v___x_2706_;
v_isShared_2718_ = v_isSharedCheck_2745_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_snapshotTasks_2715_);
lean_inc(v_infoState_2714_);
lean_inc(v_messages_2713_);
lean_inc(v_cache_2712_);
lean_inc(v_traceState_2707_);
lean_inc(v_auxDeclNGen_2711_);
lean_inc(v_ngen_2710_);
lean_inc(v_nextMacroScope_2709_);
lean_inc(v_env_2708_);
lean_dec(v___x_2706_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2745_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
uint64_t v_tid_2719_; lean_object* v_traces_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2744_; 
v_tid_2719_ = lean_ctor_get_uint64(v_traceState_2707_, sizeof(void*)*1);
v_traces_2720_ = lean_ctor_get(v_traceState_2707_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_traceState_2707_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2722_ = v_traceState_2707_;
v_isShared_2723_ = v_isSharedCheck_2744_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_traces_2720_);
lean_dec(v_traceState_2707_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2744_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; double v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2726_ = 0;
v___x_2727_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2728_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2728_, 0, v_cls_2693_);
lean_ctor_set(v___x_2728_, 1, v___x_2724_);
lean_ctor_set(v___x_2728_, 2, v___x_2727_);
lean_ctor_set_float(v___x_2728_, sizeof(void*)*3, v___x_2725_);
lean_ctor_set_float(v___x_2728_, sizeof(void*)*3 + 8, v___x_2725_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*3 + 16, v___x_2726_);
v___x_2729_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2730_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v_a_2702_);
lean_ctor_set(v___x_2730_, 2, v___x_2729_);
lean_inc(v_ref_2700_);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v_ref_2700_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = l_Lean_PersistentArray_push___redArg(v_traces_2720_, v___x_2731_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2732_);
v___x_2734_ = v___x_2722_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2732_);
lean_ctor_set_uint64(v_reuseFailAlloc_2743_, sizeof(void*)*1, v_tid_2719_);
v___x_2734_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 4, v___x_2734_);
v___x_2736_ = v___x_2717_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_env_2708_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_nextMacroScope_2709_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_ngen_2710_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_auxDeclNGen_2711_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_cache_2712_);
lean_ctor_set(v_reuseFailAlloc_2742_, 6, v_messages_2713_);
lean_ctor_set(v_reuseFailAlloc_2742_, 7, v_infoState_2714_);
lean_ctor_set(v_reuseFailAlloc_2742_, 8, v_snapshotTasks_2715_);
v___x_2736_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2737_ = lean_st_ref_set(v___y_2698_, v___x_2736_);
v___x_2738_ = lean_box(0);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2738_);
v___x_2740_ = v___x_2704_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2747_, lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2747_, v_msg_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2764_ = l_Lean_Name_append(v___x_2763_, v___x_2762_);
return v___x_2764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2767_ = l_Lean_stringToMessageData(v___x_2766_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2770_ = l_Lean_stringToMessageData(v___x_2769_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2773_ = l_Lean_stringToMessageData(v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2776_ = l_Lean_stringToMessageData(v___x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2777_, lean_object* v_fst_2778_, lean_object* v_fst_2779_, lean_object* v_inst_2780_, lean_object* v_a_2781_, lean_object* v_projInfo_x3f_2782_, lean_object* v_argVars_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2777_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v_dummy_2792_; lean_object* v_nargs_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; size_t v_sz_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v_dummy_2792_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2793_ = l_Lean_Expr_getAppNumArgs(v_a_2777_);
lean_inc(v_nargs_2793_);
v___x_2794_ = lean_mk_array(v_nargs_2793_, v_dummy_2792_);
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_nat_sub(v_nargs_2793_, v___x_2795_);
lean_dec(v_nargs_2793_);
lean_inc_ref(v_a_2777_);
v___x_2797_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2777_, v___x_2794_, v___x_2796_);
v___x_2798_ = lean_array_get_size(v___x_2797_);
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2798_);
v_sz_2801_ = lean_array_size(v___x_2797_);
v___x_2802_ = ((size_t)0ULL);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2791_, v_fst_2778_, v_argVars_2783_, v___x_2797_, v_sz_2801_, v___x_2802_, v___x_2800_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec_ref(v___x_2797_);
lean_dec(v_a_2791_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec_ref_known(v___x_2803_, 1);
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2805_ = lean_array_get_size(v_fst_2778_);
v___x_2806_ = l_List_range(v___x_2805_);
v___x_2807_ = lean_box(0);
v___x_2808_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2779_, v___x_2806_, v___x_2807_);
v___x_2809_ = lean_array_mk(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2804_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
lean_inc_ref(v_inst_2780_);
lean_inc_ref(v_argVars_2783_);
v___x_2811_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2778_, v_argVars_2783_, v_inst_2780_, v_a_2781_, v_projInfo_x3f_2782_, v___x_2810_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2904_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2904_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2904_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_fst_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2902_; 
v_fst_2816_ = lean_ctor_get(v_a_2812_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v_a_2812_, 1);
lean_dec(v_unused_2903_);
v___x_2818_ = v_a_2812_;
v_isShared_2819_ = v_isSharedCheck_2902_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_fst_2816_);
lean_dec(v_a_2812_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2902_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v_options_2824_; lean_object* v_inheritedTraceOptions_2825_; lean_object* v___y_2826_; lean_object* v_options_2882_; lean_object* v_inheritedTraceOptions_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_options_2882_ = lean_ctor_get(v___y_2787_, 2);
v_inheritedTraceOptions_2883_ = lean_ctor_get(v___y_2787_, 13);
v___x_2884_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2885_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2882_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec_ref(v_a_2777_);
v___y_2821_ = v___y_2785_;
v___y_2822_ = v___y_2786_;
v___y_2823_ = v___y_2787_;
v_options_2824_ = v_options_2882_;
v_inheritedTraceOptions_2825_ = v_inheritedTraceOptions_2883_;
v___y_2826_ = v___y_2788_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2886_; lean_object* v_a_2887_; uint8_t v___x_2888_; 
v___x_2886_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2777_, v___y_2786_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2886_);
v___x_2888_ = l_Lean_Expr_hasExprMVar(v_a_2887_);
if (v___x_2888_ == 0)
{
lean_dec(v_a_2887_);
v___y_2821_ = v___y_2785_;
v___y_2822_ = v___y_2786_;
v___y_2823_ = v___y_2787_;
v_options_2824_ = v_options_2882_;
v_inheritedTraceOptions_2825_ = v_inheritedTraceOptions_2883_;
v___y_2826_ = v___y_2788_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_del_object(v___x_2818_);
lean_dec(v_fst_2816_);
lean_del_object(v___x_2814_);
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_inst_2780_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2890_ = l_Lean_Expr_setPPExplicit(v_a_2887_, v___x_2888_);
v___x_2891_ = l_Lean_indentExpr(v___x_2890_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2889_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2892_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
v___jp_2820_:
{
uint8_t v_hasTrace_2827_; 
v_hasTrace_2827_ = lean_ctor_get_uint8(v_options_2824_, sizeof(void*)*1);
if (v_hasTrace_2827_ == 0)
{
lean_object* v___x_2829_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_inst_2780_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_fst_2816_);
v___x_2829_ = v___x_2814_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_fst_2816_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2832_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2825_, v_options_2824_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2835_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_inst_2780_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_fst_2816_);
v___x_2835_ = v___x_2814_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_fst_2816_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
else
{
size_t v_sz_2837_; lean_object* v___x_2838_; 
lean_del_object(v___x_2814_);
v_sz_2837_ = lean_array_size(v_fst_2816_);
lean_inc(v_fst_2816_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2783_, v_sz_2837_, v___x_2802_, v_fst_2816_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2826_);
lean_dec_ref(v_argVars_2783_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2841_ = l_Lean_MessageData_ofExpr(v_inst_2780_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 7);
lean_ctor_set(v___x_2818_, 1, v___x_2841_);
lean_ctor_set(v___x_2818_, 0, v___x_2840_);
v___x_2843_ = v___x_2818_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
lean_inc(v_fst_2816_);
v___x_2846_ = lean_array_to_list(v_fst_2816_);
v___x_2847_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2846_, v___x_2807_);
v___x_2848_ = l_Lean_MessageData_ofList(v___x_2847_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2845_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_array_to_list(v_a_2839_);
v___x_2853_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2854_ = l_Lean_MessageData_joinSep(v___x_2852_, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2851_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2831_, v___x_2855_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2826_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v___x_2856_, 0);
lean_dec(v_unused_2864_);
v___x_2858_ = v___x_2856_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v___x_2856_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v_fst_2816_);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_fst_2816_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_fst_2816_);
v_a_2865_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2856_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2856_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_del_object(v___x_2818_);
lean_dec(v_fst_2816_);
lean_dec_ref(v_inst_2780_);
v_a_2874_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2838_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2838_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
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
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_inst_2780_);
lean_dec_ref(v_a_2777_);
v_a_2905_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2811_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2811_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_a_2781_);
lean_dec_ref(v_inst_2780_);
lean_dec_ref(v_fst_2778_);
lean_dec_ref(v_a_2777_);
v_a_2913_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2803_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2803_);
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
}
else
{
lean_dec_ref(v_argVars_2783_);
lean_dec_ref(v_a_2781_);
lean_dec_ref(v_inst_2780_);
lean_dec_ref(v_fst_2778_);
lean_dec_ref(v_a_2777_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2921_, lean_object* v_fst_2922_, lean_object* v_fst_2923_, lean_object* v_inst_2924_, lean_object* v_a_2925_, lean_object* v_projInfo_x3f_2926_, lean_object* v_argVars_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2921_, v_fst_2922_, v_fst_2923_, v_inst_2924_, v_a_2925_, v_projInfo_x3f_2926_, v_argVars_2927_, v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v_x_2928_);
lean_dec(v_projInfo_x3f_2926_);
lean_dec_ref(v_fst_2923_);
return v_res_2934_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2935_; uint64_t v___x_2936_; 
v___x_2935_ = 2;
v___x_2936_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2937_, lean_object* v_projInfo_x3f_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; uint8_t v_foApprox_2945_; uint8_t v_ctxApprox_2946_; uint8_t v_quasiPatternApprox_2947_; uint8_t v_constApprox_2948_; uint8_t v_isDefEqStuckEx_2949_; uint8_t v_unificationHints_2950_; uint8_t v_proofIrrelevance_2951_; uint8_t v_assignSyntheticOpaque_2952_; uint8_t v_offsetCnstrs_2953_; uint8_t v_etaStruct_2954_; uint8_t v_univApprox_2955_; uint8_t v_iota_2956_; uint8_t v_beta_2957_; uint8_t v_proj_2958_; uint8_t v_zeta_2959_; uint8_t v_zetaDelta_2960_; uint8_t v_zetaUnused_2961_; uint8_t v_zetaHave_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_3027_; 
v___x_2944_ = l_Lean_Meta_Context_config(v_a_2939_);
v_foApprox_2945_ = lean_ctor_get_uint8(v___x_2944_, 0);
v_ctxApprox_2946_ = lean_ctor_get_uint8(v___x_2944_, 1);
v_quasiPatternApprox_2947_ = lean_ctor_get_uint8(v___x_2944_, 2);
v_constApprox_2948_ = lean_ctor_get_uint8(v___x_2944_, 3);
v_isDefEqStuckEx_2949_ = lean_ctor_get_uint8(v___x_2944_, 4);
v_unificationHints_2950_ = lean_ctor_get_uint8(v___x_2944_, 5);
v_proofIrrelevance_2951_ = lean_ctor_get_uint8(v___x_2944_, 6);
v_assignSyntheticOpaque_2952_ = lean_ctor_get_uint8(v___x_2944_, 7);
v_offsetCnstrs_2953_ = lean_ctor_get_uint8(v___x_2944_, 8);
v_etaStruct_2954_ = lean_ctor_get_uint8(v___x_2944_, 10);
v_univApprox_2955_ = lean_ctor_get_uint8(v___x_2944_, 11);
v_iota_2956_ = lean_ctor_get_uint8(v___x_2944_, 12);
v_beta_2957_ = lean_ctor_get_uint8(v___x_2944_, 13);
v_proj_2958_ = lean_ctor_get_uint8(v___x_2944_, 14);
v_zeta_2959_ = lean_ctor_get_uint8(v___x_2944_, 15);
v_zetaDelta_2960_ = lean_ctor_get_uint8(v___x_2944_, 16);
v_zetaUnused_2961_ = lean_ctor_get_uint8(v___x_2944_, 17);
v_zetaHave_2962_ = lean_ctor_get_uint8(v___x_2944_, 18);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2964_ = v___x_2944_;
v_isShared_2965_ = v_isSharedCheck_3027_;
goto v_resetjp_2963_;
}
else
{
lean_dec(v___x_2944_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_3027_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
uint8_t v_trackZetaDelta_2966_; lean_object* v_zetaDeltaSet_2967_; lean_object* v_lctx_2968_; lean_object* v_localInstances_2969_; lean_object* v_defEqCtx_x3f_2970_; lean_object* v_synthPendingDepth_2971_; lean_object* v_canUnfold_x3f_2972_; uint8_t v_univApprox_2973_; uint8_t v_inTypeClassResolution_2974_; uint8_t v_cacheInferType_2975_; uint8_t v___x_2976_; lean_object* v_config_2978_; 
v_trackZetaDelta_2966_ = lean_ctor_get_uint8(v_a_2939_, sizeof(void*)*7);
v_zetaDeltaSet_2967_ = lean_ctor_get(v_a_2939_, 1);
v_lctx_2968_ = lean_ctor_get(v_a_2939_, 2);
v_localInstances_2969_ = lean_ctor_get(v_a_2939_, 3);
v_defEqCtx_x3f_2970_ = lean_ctor_get(v_a_2939_, 4);
v_synthPendingDepth_2971_ = lean_ctor_get(v_a_2939_, 5);
v_canUnfold_x3f_2972_ = lean_ctor_get(v_a_2939_, 6);
v_univApprox_2973_ = lean_ctor_get_uint8(v_a_2939_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2974_ = lean_ctor_get_uint8(v_a_2939_, sizeof(void*)*7 + 2);
v_cacheInferType_2975_ = lean_ctor_get_uint8(v_a_2939_, sizeof(void*)*7 + 3);
v___x_2976_ = 2;
if (v_isShared_2965_ == 0)
{
v_config_2978_ = v___x_2964_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 0, v_foApprox_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 1, v_ctxApprox_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 2, v_quasiPatternApprox_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 3, v_constApprox_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 4, v_isDefEqStuckEx_2949_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 5, v_unificationHints_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 6, v_proofIrrelevance_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 7, v_assignSyntheticOpaque_2952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 8, v_offsetCnstrs_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 10, v_etaStruct_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 11, v_univApprox_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 12, v_iota_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 13, v_beta_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 14, v_proj_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 15, v_zeta_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 16, v_zetaDelta_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 17, v_zetaUnused_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, 18, v_zetaHave_2962_);
v_config_2978_ = v_reuseFailAlloc_3026_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
uint64_t v___x_2979_; uint64_t v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; uint64_t v_key_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_ctor_set_uint8(v_config_2978_, 9, v___x_2976_);
v___x_2979_ = l_Lean_Meta_Context_configKey(v_a_2939_);
v___x_2980_ = 3ULL;
v___x_2981_ = lean_uint64_shift_right(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_uint64_shift_left(v___x_2981_, v___x_2980_);
v___x_2983_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2984_ = lean_uint64_lor(v___x_2982_, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2985_, 0, v_config_2978_);
lean_ctor_set_uint64(v___x_2985_, sizeof(void*)*1, v_key_2984_);
lean_inc(v_canUnfold_x3f_2972_);
lean_inc(v_synthPendingDepth_2971_);
lean_inc(v_defEqCtx_x3f_2970_);
lean_inc_ref(v_localInstances_2969_);
lean_inc_ref(v_lctx_2968_);
lean_inc(v_zetaDeltaSet_2967_);
v___x_2986_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v_zetaDeltaSet_2967_);
lean_ctor_set(v___x_2986_, 2, v_lctx_2968_);
lean_ctor_set(v___x_2986_, 3, v_localInstances_2969_);
lean_ctor_set(v___x_2986_, 4, v_defEqCtx_x3f_2970_);
lean_ctor_set(v___x_2986_, 5, v_synthPendingDepth_2971_);
lean_ctor_set(v___x_2986_, 6, v_canUnfold_x3f_2972_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*7, v_trackZetaDelta_2966_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*7 + 1, v_univApprox_2973_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2974_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*7 + 3, v_cacheInferType_2975_);
lean_inc(v_a_2942_);
lean_inc_ref(v_a_2941_);
lean_inc(v_a_2940_);
lean_inc_ref(v___x_2986_);
lean_inc_ref(v_inst_2937_);
v___x_2987_ = lean_infer_type(v_inst_2937_, v___x_2986_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_n(v_a_2988_, 2);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = lean_box(0);
v___x_2990_ = 0;
v___x_2991_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2988_, v___x_2989_, v___x_2990_, v___x_2986_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_snd_2993_; lean_object* v_fst_2994_; lean_object* v_fst_2995_; lean_object* v_snd_2996_; lean_object* v___x_2997_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v_snd_2993_ = lean_ctor_get(v_a_2992_, 1);
lean_inc(v_snd_2993_);
v_fst_2994_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_fst_2994_);
lean_dec(v_a_2992_);
v_fst_2995_ = lean_ctor_get(v_snd_2993_, 0);
lean_inc(v_fst_2995_);
v_snd_2996_ = lean_ctor_get(v_snd_2993_, 1);
lean_inc(v_snd_2996_);
lean_dec(v_snd_2993_);
lean_inc(v_a_2942_);
lean_inc_ref(v_a_2941_);
lean_inc(v_a_2940_);
lean_inc_ref(v___x_2986_);
v___x_2997_ = lean_whnf(v_snd_2996_, v___x_2986_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___f_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
lean_inc(v_a_2988_);
v___f_2999_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2999_, 0, v_a_2998_);
lean_closure_set(v___f_2999_, 1, v_fst_2994_);
lean_closure_set(v___f_2999_, 2, v_fst_2995_);
lean_closure_set(v___f_2999_, 3, v_inst_2937_);
lean_closure_set(v___f_2999_, 4, v_a_2988_);
lean_closure_set(v___f_2999_, 5, v_projInfo_x3f_2938_);
v___x_3000_ = 0;
v___x_3001_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2988_, v___f_2999_, v___x_3000_, v___x_3000_, v___x_2986_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec_ref_known(v___x_2986_, 7);
return v___x_3001_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_fst_2995_);
lean_dec(v_fst_2994_);
lean_dec(v_a_2988_);
lean_dec_ref_known(v___x_2986_, 7);
lean_dec(v_projInfo_x3f_2938_);
lean_dec_ref(v_inst_2937_);
v_a_3002_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2997_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2997_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_2988_);
lean_dec_ref_known(v___x_2986_, 7);
lean_dec(v_projInfo_x3f_2938_);
lean_dec_ref(v_inst_2937_);
v_a_3010_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2991_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2991_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref_known(v___x_2986_, 7);
lean_dec(v_projInfo_x3f_2938_);
lean_dec_ref(v_inst_2937_);
v_a_3018_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2987_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2987_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3028_, lean_object* v_projInfo_x3f_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3028_, v_projInfo_x3f_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3036_, lean_object* v___x_3037_, lean_object* v_a_3038_, lean_object* v_inst_3039_, lean_object* v_R_3040_, lean_object* v_a_3041_, lean_object* v_b_3042_, lean_object* v_c_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3036_, v___x_3037_, v_a_3038_, v_a_3041_, v_b_3042_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3050_, lean_object* v___x_3051_, lean_object* v_a_3052_, lean_object* v_inst_3053_, lean_object* v_R_3054_, lean_object* v_a_3055_, lean_object* v_b_3056_, lean_object* v_c_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3050_, v___x_3051_, v_a_3052_, v_inst_3053_, v_R_3054_, v_a_3055_, v_b_3056_, v_c_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_a_3052_);
lean_dec(v___x_3051_);
lean_dec(v_upperBound_3050_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3064_, lean_object* v_msg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3072_, lean_object* v_msg_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3072_, v_msg_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3080_, lean_object* v_argVars_3081_, lean_object* v_inst_3082_, lean_object* v_a_3083_, lean_object* v_projInfo_x3f_3084_, lean_object* v_inst_3085_, lean_object* v_a_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3080_, v_argVars_3081_, v_inst_3082_, v_a_3083_, v_projInfo_x3f_3084_, v_a_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3093_, lean_object* v_argVars_3094_, lean_object* v_inst_3095_, lean_object* v_a_3096_, lean_object* v_projInfo_x3f_3097_, lean_object* v_inst_3098_, lean_object* v_a_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3093_, v_argVars_3094_, v_inst_3095_, v_a_3096_, v_projInfo_x3f_3097_, v_inst_3098_, v_a_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v_projInfo_x3f_3097_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3106_, lean_object* v_k_3107_, uint8_t v_cleanupAnnotations_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___f_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3114_, 0, v_k_3107_);
v___x_3115_ = 0;
v___x_3116_ = lean_box(0);
v___x_3117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3115_, v___x_3116_, v_type_3106_, v___f_3114_, v_cleanupAnnotations_3108_, v___x_3115_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
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
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
v_a_3126_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3117_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3117_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3134_, lean_object* v_k_3135_, lean_object* v_cleanupAnnotations_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3142_; lean_object* v_res_3143_; 
v_cleanupAnnotations_boxed_3142_ = lean_unbox(v_cleanupAnnotations_3136_);
v_res_3143_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3134_, v_k_3135_, v_cleanupAnnotations_boxed_3142_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3144_, lean_object* v_type_3145_, lean_object* v_k_3146_, uint8_t v_cleanupAnnotations_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3145_, v_k_3146_, v_cleanupAnnotations_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_type_3155_, lean_object* v_k_3156_, lean_object* v_cleanupAnnotations_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3163_; lean_object* v_res_3164_; 
v_cleanupAnnotations_boxed_3163_ = lean_unbox(v_cleanupAnnotations_3157_);
v_res_3164_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3154_, v_type_3155_, v_k_3156_, v_cleanupAnnotations_boxed_3163_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object* v_as_3165_, size_t v_sz_3166_, size_t v_i_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_a_3175_; uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_lt(v_i_3167_, v_sz_3166_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_b_3168_);
return v___x_3180_;
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_a_3181_ = lean_array_uget_borrowed(v_as_3165_, v_i_3167_);
v___x_3182_ = l_Lean_Expr_fvarId_x21(v_a_3181_);
lean_inc(v___x_3182_);
v___x_3183_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3182_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; uint8_t v___x_3187_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = lean_box(0);
v___x_3186_ = lean_unbox(v_a_3184_);
lean_dec(v_a_3184_);
v___x_3187_ = l_Lean_BinderInfo_isInstImplicit(v___x_3186_);
if (v___x_3187_ == 0)
{
lean_dec(v___x_3182_);
v_a_3175_ = v___x_3185_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_st_ref_take(v___y_3169_);
v___x_3189_ = l_Lean_CollectFVars_State_add(v___x_3188_, v___x_3182_);
v___x_3190_ = lean_st_ref_set(v___y_3169_, v___x_3189_);
v_a_3175_ = v___x_3185_;
goto v___jp_3174_;
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v___x_3182_);
v_a_3191_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3183_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3183_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
v___jp_3174_:
{
size_t v___x_3176_; size_t v___x_3177_; 
v___x_3176_ = ((size_t)1ULL);
v___x_3177_ = lean_usize_add(v_i_3167_, v___x_3176_);
v_i_3167_ = v___x_3177_;
v_b_3168_ = v_a_3175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object* v_as_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3199_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v_as_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3211_, lean_object* v_t_3212_){
_start:
{
if (lean_obj_tag(v_t_3212_) == 0)
{
lean_object* v_k_3213_; lean_object* v_l_3214_; lean_object* v_r_3215_; uint8_t v___x_3216_; 
v_k_3213_ = lean_ctor_get(v_t_3212_, 1);
v_l_3214_ = lean_ctor_get(v_t_3212_, 3);
v_r_3215_ = lean_ctor_get(v_t_3212_, 4);
v___x_3216_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3211_, v_k_3213_);
switch(v___x_3216_)
{
case 0:
{
v_t_3212_ = v_l_3214_;
goto _start;
}
case 1:
{
uint8_t v___x_3218_; 
v___x_3218_ = 1;
return v___x_3218_;
}
default: 
{
v_t_3212_ = v_r_3215_;
goto _start;
}
}
}
else
{
uint8_t v___x_3220_; 
v___x_3220_ = 0;
return v___x_3220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3221_, lean_object* v_t_3222_){
_start:
{
uint8_t v_res_3223_; lean_object* v_r_3224_; 
v_res_3223_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3221_, v_t_3222_);
lean_dec(v_t_3222_);
lean_dec(v_k_3221_);
v_r_3224_ = lean_box(v_res_3223_);
return v_r_3224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3231_, lean_object* v_as_3232_, size_t v_sz_3233_, size_t v_i_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_a_3241_; uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3234_, v_sz_3233_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_b_3235_);
return v___x_3246_;
}
else
{
lean_object* v_snd_3247_; 
v_snd_3247_ = lean_ctor_get(v_b_3235_, 1);
lean_inc(v_snd_3247_);
if (lean_obj_tag(v_snd_3247_) == 0)
{
lean_object* v_fst_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3256_; 
v_fst_3248_ = lean_ctor_get(v_b_3235_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_b_3235_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v_b_3235_, 1);
lean_dec(v_unused_3257_);
v___x_3250_ = v_b_3235_;
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_fst_3248_);
lean_dec(v_b_3235_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_fst_3248_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_snd_3247_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
return v___x_3254_;
}
}
}
else
{
lean_object* v_fst_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3315_; 
v_fst_3258_ = lean_ctor_get(v_b_3235_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_b_3235_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_b_3235_, 1);
lean_dec(v_unused_3316_);
v___x_3260_ = v_b_3235_;
v_isShared_3261_ = v_isSharedCheck_3315_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_fst_3258_);
lean_dec(v_b_3235_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3315_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_val_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3314_; 
v_val_3262_ = lean_ctor_get(v_snd_3247_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_snd_3247_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3264_ = v_snd_3247_;
v_isShared_3265_ = v_isSharedCheck_3314_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_val_3262_);
lean_dec(v_snd_3247_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3314_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v_fvarSet_3266_; lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v_fvarSet_3266_ = lean_ctor_get(v_a_3231_, 1);
v_a_3267_ = lean_array_uget_borrowed(v_as_3232_, v_i_3234_);
v___x_3268_ = lean_unsigned_to_nat(1u);
v___x_3269_ = lean_nat_add(v_val_3262_, v___x_3268_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3269_);
v___x_3271_ = v___x_3264_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = l_Lean_Expr_fvarId_x21(v_a_3267_);
v___x_3273_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3272_, v_fvarSet_3266_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_FVarId_getDecl___redArg(v___x_3272_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_LocalDecl_ppAsBinder(v_a_3275_);
if (lean_obj_tag(v___x_3276_) == 1)
{
lean_object* v_val_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3298_; 
v_val_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3298_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_val_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3298_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3282_ = l_Nat_reprFast(v_val_3262_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 3);
lean_ctor_set(v___x_3279_, 0, v___x_3282_);
v___x_3284_ = v___x_3279_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3285_ = l_Lean_MessageData_ofFormat(v___x_3284_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3281_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_val_3277_);
v___x_3290_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Lean_indentD(v___x_3291_);
v___x_3293_ = lean_array_push(v_fst_3258_, v___x_3292_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3271_);
lean_ctor_set(v___x_3260_, 0, v___x_3293_);
v___x_3295_ = v___x_3260_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___x_3271_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
v_a_3241_ = v___x_3295_;
goto v___jp_3240_;
}
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___x_3276_);
lean_dec(v_val_3262_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3271_);
v___x_3300_ = v___x_3260_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_fst_3258_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3271_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
v_a_3241_ = v___x_3300_;
goto v___jp_3240_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v___x_3271_);
lean_dec(v_val_3262_);
lean_del_object(v___x_3260_);
lean_dec(v_fst_3258_);
v_a_3302_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3274_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3274_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v___x_3311_; 
lean_dec(v___x_3272_);
lean_dec(v_val_3262_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3271_);
v___x_3311_ = v___x_3260_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_fst_3258_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3271_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
v_a_3241_ = v___x_3311_;
goto v___jp_3240_;
}
}
}
}
}
}
}
v___jp_3240_:
{
size_t v___x_3242_; size_t v___x_3243_; 
v___x_3242_ = ((size_t)1ULL);
v___x_3243_ = lean_usize_add(v_i_3234_, v___x_3242_);
v_i_3234_ = v___x_3243_;
v_b_3235_ = v_a_3241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3317_, lean_object* v_as_3318_, lean_object* v_sz_3319_, lean_object* v_i_3320_, lean_object* v_b_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
size_t v_sz_boxed_3326_; size_t v_i_boxed_3327_; lean_object* v_res_3328_; 
v_sz_boxed_3326_ = lean_unbox_usize(v_sz_3319_);
lean_dec(v_sz_3319_);
v_i_boxed_3327_ = lean_unbox_usize(v_i_3320_);
lean_dec(v_i_3320_);
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3317_, v_as_3318_, v_sz_boxed_3326_, v_i_boxed_3327_, v_b_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v_as_3318_);
lean_dec_ref(v_a_3317_);
return v_res_3328_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3336_, uint8_t v_suppressElabErrors_3337_, lean_object* v_x_3338_){
_start:
{
if (lean_obj_tag(v_x_3338_) == 1)
{
lean_object* v_pre_3339_; 
v_pre_3339_ = lean_ctor_get(v_x_3338_, 0);
switch(lean_obj_tag(v_pre_3339_))
{
case 1:
{
lean_object* v_pre_3340_; 
v_pre_3340_ = lean_ctor_get(v_pre_3339_, 0);
switch(lean_obj_tag(v_pre_3340_))
{
case 0:
{
lean_object* v_str_3341_; lean_object* v_str_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_str_3341_ = lean_ctor_get(v_x_3338_, 1);
v_str_3342_ = lean_ctor_get(v_pre_3339_, 1);
v___x_3343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3344_ = lean_string_dec_eq(v_str_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3346_ = lean_string_dec_eq(v_str_3342_, v___x_3345_);
if (v___x_3346_ == 0)
{
return v___y_3336_;
}
else
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3348_ = lean_string_dec_eq(v_str_3341_, v___x_3347_);
if (v___x_3348_ == 0)
{
return v___y_3336_;
}
else
{
return v_suppressElabErrors_3337_;
}
}
}
else
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3350_ = lean_string_dec_eq(v_str_3341_, v___x_3349_);
if (v___x_3350_ == 0)
{
return v___y_3336_;
}
else
{
return v_suppressElabErrors_3337_;
}
}
}
case 1:
{
lean_object* v_pre_3351_; 
v_pre_3351_ = lean_ctor_get(v_pre_3340_, 0);
if (lean_obj_tag(v_pre_3351_) == 0)
{
lean_object* v_str_3352_; lean_object* v_str_3353_; lean_object* v_str_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_str_3352_ = lean_ctor_get(v_x_3338_, 1);
v_str_3353_ = lean_ctor_get(v_pre_3339_, 1);
v_str_3354_ = lean_ctor_get(v_pre_3340_, 1);
v___x_3355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3356_ = lean_string_dec_eq(v_str_3354_, v___x_3355_);
if (v___x_3356_ == 0)
{
return v___y_3336_;
}
else
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3358_ = lean_string_dec_eq(v_str_3353_, v___x_3357_);
if (v___x_3358_ == 0)
{
return v___y_3336_;
}
else
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3360_ = lean_string_dec_eq(v_str_3352_, v___x_3359_);
if (v___x_3360_ == 0)
{
return v___y_3336_;
}
else
{
return v_suppressElabErrors_3337_;
}
}
}
}
else
{
return v___y_3336_;
}
}
default: 
{
return v___y_3336_;
}
}
}
case 0:
{
lean_object* v_str_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_str_3361_ = lean_ctor_get(v_x_3338_, 1);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3363_ = lean_string_dec_eq(v_str_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
return v___y_3336_;
}
else
{
return v_suppressElabErrors_3337_;
}
}
default: 
{
return v___y_3336_;
}
}
}
else
{
return v___y_3336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3364_, lean_object* v_suppressElabErrors_3365_, lean_object* v_x_3366_){
_start:
{
uint8_t v___y_11867__boxed_3367_; uint8_t v_suppressElabErrors_boxed_3368_; uint8_t v_res_3369_; lean_object* v_r_3370_; 
v___y_11867__boxed_3367_ = lean_unbox(v___y_3364_);
v_suppressElabErrors_boxed_3368_ = lean_unbox(v_suppressElabErrors_3365_);
v_res_3369_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11867__boxed_3367_, v_suppressElabErrors_boxed_3368_, v_x_3366_);
lean_dec(v_x_3366_);
v_r_3370_ = lean_box(v_res_3369_);
return v_r_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3371_, lean_object* v_msgData_3372_, uint8_t v_severity_3373_, uint8_t v_isSilent_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3417_; uint8_t v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3453_; uint8_t v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; uint8_t v___y_3458_; uint8_t v___y_3459_; uint8_t v___x_3464_; uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; uint8_t v___y_3472_; uint8_t v___y_3474_; uint8_t v___x_3489_; 
v___x_3464_ = 2;
v___x_3489_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3373_, v___x_3464_);
if (v___x_3489_ == 0)
{
v___y_3474_ = v___x_3489_;
goto v___jp_3473_;
}
else
{
uint8_t v___x_3490_; 
lean_inc_ref(v_msgData_3372_);
v___x_3490_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3372_);
v___y_3474_ = v___x_3490_;
goto v___jp_3473_;
}
v___jp_3380_:
{
lean_object* v___x_3390_; lean_object* v_currNamespace_3391_; lean_object* v_openDecls_3392_; lean_object* v_env_3393_; lean_object* v_nextMacroScope_3394_; lean_object* v_ngen_3395_; lean_object* v_auxDeclNGen_3396_; lean_object* v_traceState_3397_; lean_object* v_cache_3398_; lean_object* v_messages_3399_; lean_object* v_infoState_3400_; lean_object* v_snapshotTasks_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3415_; 
v___x_3390_ = lean_st_ref_take(v___y_3389_);
v_currNamespace_3391_ = lean_ctor_get(v___y_3388_, 6);
v_openDecls_3392_ = lean_ctor_get(v___y_3388_, 7);
v_env_3393_ = lean_ctor_get(v___x_3390_, 0);
v_nextMacroScope_3394_ = lean_ctor_get(v___x_3390_, 1);
v_ngen_3395_ = lean_ctor_get(v___x_3390_, 2);
v_auxDeclNGen_3396_ = lean_ctor_get(v___x_3390_, 3);
v_traceState_3397_ = lean_ctor_get(v___x_3390_, 4);
v_cache_3398_ = lean_ctor_get(v___x_3390_, 5);
v_messages_3399_ = lean_ctor_get(v___x_3390_, 6);
v_infoState_3400_ = lean_ctor_get(v___x_3390_, 7);
v_snapshotTasks_3401_ = lean_ctor_get(v___x_3390_, 8);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3403_ = v___x_3390_;
v_isShared_3404_ = v_isSharedCheck_3415_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snapshotTasks_3401_);
lean_inc(v_infoState_3400_);
lean_inc(v_messages_3399_);
lean_inc(v_cache_3398_);
lean_inc(v_traceState_3397_);
lean_inc(v_auxDeclNGen_3396_);
lean_inc(v_ngen_3395_);
lean_inc(v_nextMacroScope_3394_);
lean_inc(v_env_3393_);
lean_dec(v___x_3390_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3415_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
lean_inc(v_openDecls_3392_);
lean_inc(v_currNamespace_3391_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_currNamespace_3391_);
lean_ctor_set(v___x_3405_, 1, v_openDecls_3392_);
v___x_3406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___y_3387_);
lean_inc_ref(v___y_3381_);
lean_inc_ref(v___y_3383_);
v___x_3407_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3407_, 0, v___y_3383_);
lean_ctor_set(v___x_3407_, 1, v___y_3386_);
lean_ctor_set(v___x_3407_, 2, v___y_3382_);
lean_ctor_set(v___x_3407_, 3, v___y_3381_);
lean_ctor_set(v___x_3407_, 4, v___x_3406_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*5, v___y_3385_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*5 + 1, v___y_3384_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*5 + 2, v_isSilent_3374_);
v___x_3408_ = l_Lean_MessageLog_add(v___x_3407_, v_messages_3399_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 6, v___x_3408_);
v___x_3410_ = v___x_3403_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_env_3393_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_nextMacroScope_3394_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_ngen_3395_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_auxDeclNGen_3396_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_traceState_3397_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v_cache_3398_);
lean_ctor_set(v_reuseFailAlloc_3414_, 6, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3414_, 7, v_infoState_3400_);
lean_ctor_set(v_reuseFailAlloc_3414_, 8, v_snapshotTasks_3401_);
v___x_3410_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = lean_st_ref_set(v___y_3389_, v___x_3410_);
v___x_3412_ = lean_box(0);
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
}
}
v___jp_3416_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3440_; 
v___x_3425_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3372_);
v___x_3426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3425_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3440_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3440_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_inc_ref_n(v___y_3420_, 2);
v___x_3431_ = l_Lean_FileMap_toPosition(v___y_3420_, v___y_3419_);
lean_dec(v___y_3419_);
v___x_3432_ = l_Lean_FileMap_toPosition(v___y_3420_, v___y_3424_);
lean_dec(v___y_3424_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
v___x_3434_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3418_ == 0)
{
lean_del_object(v___x_3429_);
lean_dec_ref(v___y_3417_);
v___y_3381_ = v___x_3434_;
v___y_3382_ = v___x_3433_;
v___y_3383_ = v___y_3421_;
v___y_3384_ = v___y_3423_;
v___y_3385_ = v___y_3422_;
v___y_3386_ = v___x_3431_;
v___y_3387_ = v_a_3427_;
v___y_3388_ = v___y_3377_;
v___y_3389_ = v___y_3378_;
goto v___jp_3380_;
}
else
{
uint8_t v___x_3435_; 
lean_inc(v_a_3427_);
v___x_3435_ = l_Lean_MessageData_hasTag(v___y_3417_, v_a_3427_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
lean_dec_ref_known(v___x_3433_, 1);
lean_dec_ref(v___x_3431_);
lean_dec(v_a_3427_);
v___x_3436_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3436_);
v___x_3438_ = v___x_3429_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
else
{
lean_del_object(v___x_3429_);
v___y_3381_ = v___x_3434_;
v___y_3382_ = v___x_3433_;
v___y_3383_ = v___y_3421_;
v___y_3384_ = v___y_3423_;
v___y_3385_ = v___y_3422_;
v___y_3386_ = v___x_3431_;
v___y_3387_ = v_a_3427_;
v___y_3388_ = v___y_3377_;
v___y_3389_ = v___y_3378_;
goto v___jp_3380_;
}
}
}
}
v___jp_3441_:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Syntax_getTailPos_x3f(v___y_3448_, v___y_3447_);
lean_dec(v___y_3448_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_inc(v___y_3449_);
v___y_3417_ = v___y_3442_;
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3444_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3447_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3449_;
goto v___jp_3416_;
}
else
{
lean_object* v_val_3451_; 
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___y_3417_ = v___y_3442_;
v___y_3418_ = v___y_3443_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3444_;
v___y_3421_ = v___y_3445_;
v___y_3422_ = v___y_3447_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v_val_3451_;
goto v___jp_3416_;
}
}
v___jp_3452_:
{
lean_object* v_ref_3460_; lean_object* v___x_3461_; 
v_ref_3460_ = l_Lean_replaceRef(v_ref_3371_, v___y_3457_);
v___x_3461_ = l_Lean_Syntax_getPos_x3f(v_ref_3460_, v___y_3458_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_unsigned_to_nat(0u);
v___y_3442_ = v___y_3453_;
v___y_3443_ = v___y_3454_;
v___y_3444_ = v___y_3455_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v___y_3459_;
v___y_3447_ = v___y_3458_;
v___y_3448_ = v_ref_3460_;
v___y_3449_ = v___x_3462_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3461_, 1);
v___y_3442_ = v___y_3453_;
v___y_3443_ = v___y_3454_;
v___y_3444_ = v___y_3455_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v___y_3459_;
v___y_3447_ = v___y_3458_;
v___y_3448_ = v_ref_3460_;
v___y_3449_ = v_val_3463_;
goto v___jp_3441_;
}
}
v___jp_3465_:
{
if (v___y_3472_ == 0)
{
v___y_3453_ = v___y_3467_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3470_;
v___y_3457_ = v___y_3469_;
v___y_3458_ = v___y_3471_;
v___y_3459_ = v_severity_3373_;
goto v___jp_3452_;
}
else
{
v___y_3453_ = v___y_3467_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3470_;
v___y_3457_ = v___y_3469_;
v___y_3458_ = v___y_3471_;
v___y_3459_ = v___x_3464_;
goto v___jp_3452_;
}
}
v___jp_3473_:
{
if (v___y_3474_ == 0)
{
lean_object* v_fileName_3475_; lean_object* v_fileMap_3476_; lean_object* v_options_3477_; lean_object* v_ref_3478_; uint8_t v_suppressElabErrors_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___f_3482_; uint8_t v___x_3483_; uint8_t v___x_3484_; 
v_fileName_3475_ = lean_ctor_get(v___y_3377_, 0);
v_fileMap_3476_ = lean_ctor_get(v___y_3377_, 1);
v_options_3477_ = lean_ctor_get(v___y_3377_, 2);
v_ref_3478_ = lean_ctor_get(v___y_3377_, 5);
v_suppressElabErrors_3479_ = lean_ctor_get_uint8(v___y_3377_, sizeof(void*)*14 + 1);
v___x_3480_ = lean_box(v___y_3474_);
v___x_3481_ = lean_box(v_suppressElabErrors_3479_);
v___f_3482_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3482_, 0, v___x_3480_);
lean_closure_set(v___f_3482_, 1, v___x_3481_);
v___x_3483_ = 1;
v___x_3484_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3373_, v___x_3483_);
if (v___x_3484_ == 0)
{
v___y_3466_ = v_suppressElabErrors_3479_;
v___y_3467_ = v___f_3482_;
v___y_3468_ = v_fileMap_3476_;
v___y_3469_ = v_ref_3478_;
v___y_3470_ = v_fileName_3475_;
v___y_3471_ = v___y_3474_;
v___y_3472_ = v___x_3484_;
goto v___jp_3465_;
}
else
{
lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3485_ = l_Lean_warningAsError;
v___x_3486_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3477_, v___x_3485_);
v___y_3466_ = v_suppressElabErrors_3479_;
v___y_3467_ = v___f_3482_;
v___y_3468_ = v_fileMap_3476_;
v___y_3469_ = v_ref_3478_;
v___y_3470_ = v_fileName_3475_;
v___y_3471_ = v___y_3474_;
v___y_3472_ = v___x_3486_;
goto v___jp_3465_;
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_msgData_3372_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3491_, lean_object* v_msgData_3492_, lean_object* v_severity_3493_, lean_object* v_isSilent_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v_severity_boxed_3500_; uint8_t v_isSilent_boxed_3501_; lean_object* v_res_3502_; 
v_severity_boxed_3500_ = lean_unbox(v_severity_3493_);
v_isSilent_boxed_3501_ = lean_unbox(v_isSilent_3494_);
v_res_3502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3491_, v_msgData_3492_, v_severity_boxed_3500_, v_isSilent_boxed_3501_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v_ref_3491_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3503_, uint8_t v_severity_3504_, uint8_t v_isSilent_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_ref_3511_; lean_object* v___x_3512_; 
v_ref_3511_ = lean_ctor_get(v___y_3508_, 5);
v___x_3512_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3511_, v_msgData_3503_, v_severity_3504_, v_isSilent_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3513_, lean_object* v_severity_3514_, lean_object* v_isSilent_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v_severity_boxed_3521_; uint8_t v_isSilent_boxed_3522_; lean_object* v_res_3523_; 
v_severity_boxed_3521_ = lean_unbox(v_severity_3514_);
v_isSilent_boxed_3522_ = lean_unbox(v_isSilent_3515_);
v_res_3523_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3513_, v_severity_boxed_3521_, v_isSilent_boxed_3522_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
uint8_t v___x_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = 1;
v___x_3531_ = 0;
v___x_3532_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3524_, v___x_3530_, v___x_3531_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_unsigned_to_nat(16u);
v___x_3548_ = lean_mk_array(v___x_3547_, v___x_3546_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3554_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3555_ = lean_box(1);
v___x_3556_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3555_);
lean_ctor_set(v___x_3557_, 2, v___x_3554_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3570_, lean_object* v_args_3571_, lean_object* v_ty_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___y_3653_; lean_object* v___x_3654_; 
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3597_ = lean_st_mk_ref(v___x_3596_);
v___x_3654_ = l_Lean_Expr_collectFVars(v_ty_3572_, v___x_3597_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v___x_3655_; size_t v_sz_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
lean_dec_ref_known(v___x_3654_, 1);
v___x_3655_ = lean_box(0);
v_sz_3656_ = lean_array_size(v_args_3571_);
v___x_3657_ = ((size_t)0ULL);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3571_, v_sz_3656_, v___x_3657_, v___x_3655_, v___x_3597_, v___y_3573_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_dec_ref_known(v___x_3658_, 1);
goto v___jp_3598_;
}
else
{
v___y_3653_ = v___x_3658_;
goto v___jp_3652_;
}
}
else
{
v___y_3653_ = v___x_3654_;
goto v___jp_3652_;
}
v___jp_3578_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
lean_inc_ref(v___y_3581_);
v___x_3582_ = l_Lean_stringToMessageData(v___y_3581_);
v___x_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___y_3579_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_array_to_list(v___y_3580_);
v___x_3587_ = l_Lean_MessageData_nil;
v___x_3588_ = l_Lean_MessageData_joinSep(v___x_3586_, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3585_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Lean_Expr_hasSorry(v___x_3570_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3591_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3593_;
}
else
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3591_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3594_;
}
}
v___jp_3598_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_st_ref_get(v___x_3597_);
lean_dec(v___x_3597_);
v___x_3600_ = l_Lean_CollectFVars_State_addDependencies(v___x_3599_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; size_t v_sz_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = lean_unsigned_to_nat(1u);
v___x_3603_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v_sz_3604_ = lean_array_size(v_args_3571_);
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3601_, v_args_3571_, v_sz_3604_, v___x_3605_, v___x_3603_, v___y_3573_, v___y_3575_, v___y_3576_);
lean_dec(v_a_3601_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3635_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3635_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3635_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_fst_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3633_; 
v_fst_3611_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v_a_3607_, 1);
lean_dec(v_unused_3634_);
v___x_3613_ = v_a_3607_;
v_isShared_3614_ = v_isSharedCheck_3633_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_fst_3611_);
lean_dec(v_a_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3633_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3615_ = lean_array_get_size(v_fst_3611_);
v___x_3616_ = lean_nat_dec_eq(v___x_3615_, v___x_3595_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_del_object(v___x_3609_);
v___x_3617_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3618_ = l_Nat_reprFast(v___x_3615_);
v___x_3619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___x_3620_ = l_Lean_MessageData_ofFormat(v___x_3619_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 7);
lean_ctor_set(v___x_3613_, 1, v___x_3620_);
lean_ctor_set(v___x_3613_, 0, v___x_3617_);
v___x_3622_ = v___x_3613_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3623_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = lean_nat_dec_eq(v___x_3615_, v___x_3602_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; 
v___x_3626_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14));
v___y_3579_ = v___x_3624_;
v___y_3580_ = v_fst_3611_;
v___y_3581_ = v___x_3626_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3627_; 
v___x_3627_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3579_ = v___x_3624_;
v___y_3580_ = v_fst_3611_;
v___y_3581_ = v___x_3627_;
goto v___jp_3578_;
}
}
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
lean_del_object(v___x_3613_);
lean_dec(v_fst_3611_);
v___x_3629_ = lean_box(0);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3629_);
v___x_3631_ = v___x_3609_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_a_3636_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3606_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3606_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3600_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3600_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
v___jp_3652_:
{
if (lean_obj_tag(v___y_3653_) == 0)
{
lean_dec_ref_known(v___y_3653_, 1);
goto v___jp_3598_;
}
else
{
lean_dec(v___x_3597_);
return v___y_3653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3659_, lean_object* v_args_3660_, lean_object* v_ty_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3659_, v_args_3660_, v_ty_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_args_3660_);
lean_dec_ref(v___x_3659_);
return v_res_3667_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_Expr_cleanupAnnotations(v_e_3668_);
switch(lean_obj_tag(v___x_3669_))
{
case 7:
{
lean_object* v_body_3670_; uint8_t v_binderInfo_3671_; uint8_t v___x_3672_; 
v_body_3670_ = lean_ctor_get(v___x_3669_, 2);
lean_inc_ref(v_body_3670_);
v_binderInfo_3671_ = lean_ctor_get_uint8(v___x_3669_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3669_, 3);
v___x_3672_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = lean_unsigned_to_nat(0u);
v___x_3674_ = lean_expr_has_loose_bvar(v_body_3670_, v___x_3673_);
if (v___x_3674_ == 0)
{
uint8_t v___x_3675_; 
lean_dec_ref(v_body_3670_);
v___x_3675_ = 1;
return v___x_3675_;
}
else
{
v_e_3668_ = v_body_3670_;
goto _start;
}
}
else
{
v_e_3668_ = v_body_3670_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3678_; 
v_body_3678_ = lean_ctor_get(v___x_3669_, 3);
lean_inc_ref(v_body_3678_);
lean_dec_ref_known(v___x_3669_, 4);
v_e_3668_ = v_body_3678_;
goto _start;
}
default: 
{
uint8_t v___x_3680_; 
lean_dec_ref(v___x_3669_);
v___x_3680_ = 0;
return v___x_3680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3681_){
_start:
{
uint8_t v_res_3682_; lean_object* v_r_3683_; 
v_res_3682_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3681_);
v_r_3683_ = lean_box(v_res_3682_);
return v_r_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3690_ = l_Lean_ConstantInfo_type(v_cinfo_3684_);
lean_inc_ref(v___x_3690_);
v___x_3691_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_dec_ref(v___x_3690_);
v___x_3692_ = lean_box(0);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
else
{
lean_object* v___f_3694_; uint8_t v___x_3695_; lean_object* v___x_3696_; 
lean_inc_ref(v___x_3690_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3694_, 0, v___x_3690_);
v___x_3695_ = 0;
v___x_3696_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3690_, v___f_3694_, v___x_3695_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
return v___x_3696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
lean_dec(v_a_3701_);
lean_dec_ref(v_a_3700_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec_ref(v_cinfo_3697_);
return v_res_3703_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3704_, lean_object* v_k_3705_, lean_object* v_t_3706_){
_start:
{
uint8_t v___x_3707_; 
v___x_3707_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3705_, v_t_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3708_, lean_object* v_k_3709_, lean_object* v_t_3710_){
_start:
{
uint8_t v_res_3711_; lean_object* v_r_3712_; 
v_res_3711_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3708_, v_k_3709_, v_t_3710_);
lean_dec(v_t_3710_);
lean_dec(v_k_3709_);
v_r_3712_ = lean_box(v_res_3711_);
return v_r_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3713_, lean_object* v_as_3714_, size_t v_sz_3715_, size_t v_i_3716_, lean_object* v_b_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3713_, v_as_3714_, v_sz_3715_, v_i_3716_, v_b_3717_, v___y_3718_, v___y_3720_, v___y_3721_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3724_, lean_object* v_as_3725_, lean_object* v_sz_3726_, lean_object* v_i_3727_, lean_object* v_b_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
size_t v_sz_boxed_3734_; size_t v_i_boxed_3735_; lean_object* v_res_3736_; 
v_sz_boxed_3734_ = lean_unbox_usize(v_sz_3726_);
lean_dec(v_sz_3726_);
v_i_boxed_3735_ = lean_unbox_usize(v_i_3727_);
lean_dec(v_i_3727_);
v_res_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3724_, v_as_3725_, v_sz_boxed_3734_, v_i_boxed_3735_, v_b_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec_ref(v_as_3725_);
lean_dec_ref(v_a_3724_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3737_, size_t v_sz_3738_, size_t v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3737_, v_sz_3738_, v_i_3739_, v_b_3740_, v___y_3741_, v___y_3742_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3748_, lean_object* v_sz_3749_, lean_object* v_i_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
size_t v_sz_boxed_3758_; size_t v_i_boxed_3759_; lean_object* v_res_3760_; 
v_sz_boxed_3758_ = lean_unbox_usize(v_sz_3749_);
lean_dec(v_sz_3749_);
v_i_boxed_3759_ = lean_unbox_usize(v_i_3750_);
lean_dec(v_i_3750_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3748_, v_sz_boxed_3758_, v_i_boxed_3759_, v_b_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v_as_3748_);
return v_res_3760_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3763_ = l_Lean_stringToMessageData(v___x_3762_);
return v___x_3763_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3766_ = l_Lean_stringToMessageData(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3769_ = l_Lean_stringToMessageData(v___x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3770_, lean_object* v_x_3771_, lean_object* v_target_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
lean_inc_ref(v_target_3772_);
v___x_3778_ = l_Lean_Meta_isClass_x3f(v_target_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3797_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3797_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3797_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
if (lean_obj_tag(v_a_3779_) == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_del_object(v___x_3781_);
v___x_3783_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3784_ = l_Lean_MessageData_ofExpr(v_c_3770_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = l_Lean_MessageData_ofExpr(v_target_3772_);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3791_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec_ref_known(v_a_3779_, 1);
lean_dec_ref(v_target_3772_);
lean_dec_ref(v_c_3770_);
v___x_3793_ = lean_box(0);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3793_);
v___x_3795_ = v___x_3781_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v_target_3772_);
lean_dec_ref(v_c_3770_);
v_a_3798_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3778_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3778_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3806_, lean_object* v_x_3807_, lean_object* v_target_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3806_, v_x_3807_, v_target_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_x_3807_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___x_3821_; 
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc_ref(v_c_3815_);
v___x_3821_ = lean_infer_type(v_c_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___f_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3823_, 0, v_c_3815_);
v___x_3824_ = 0;
v___x_3825_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3822_, v___f_3823_, v___x_3824_, v___x_3824_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_c_3815_);
v_a_3826_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3821_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3821_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_checkNonClassInstance(v_c_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; lean_object* v_env_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3844_ = lean_st_ref_get(v___y_3842_);
v_env_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc_ref(v_env_3845_);
lean_dec(v___x_3844_);
v___x_3846_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3845_, v_declName_3841_);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3848_, v___y_3849_);
lean_dec(v___y_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3852_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3865_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3866_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
return v___x_3870_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3872_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
lean_ctor_set(v___x_3872_, 2, v___x_3871_);
lean_ctor_set(v___x_3872_, 3, v___x_3871_);
lean_ctor_set(v___x_3872_, 4, v___x_3871_);
lean_ctor_set(v___x_3872_, 5, v___x_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3873_, lean_object* v_b_3874_, uint8_t v_kind_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_currNamespace_3880_; lean_object* v___x_3881_; lean_object* v_env_3882_; lean_object* v_nextMacroScope_3883_; lean_object* v_ngen_3884_; lean_object* v_auxDeclNGen_3885_; lean_object* v_traceState_3886_; lean_object* v_messages_3887_; lean_object* v_infoState_3888_; lean_object* v_snapshotTasks_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3916_; 
v_currNamespace_3880_ = lean_ctor_get(v___y_3877_, 6);
v___x_3881_ = lean_st_ref_take(v___y_3878_);
v_env_3882_ = lean_ctor_get(v___x_3881_, 0);
v_nextMacroScope_3883_ = lean_ctor_get(v___x_3881_, 1);
v_ngen_3884_ = lean_ctor_get(v___x_3881_, 2);
v_auxDeclNGen_3885_ = lean_ctor_get(v___x_3881_, 3);
v_traceState_3886_ = lean_ctor_get(v___x_3881_, 4);
v_messages_3887_ = lean_ctor_get(v___x_3881_, 6);
v_infoState_3888_ = lean_ctor_get(v___x_3881_, 7);
v_snapshotTasks_3889_ = lean_ctor_get(v___x_3881_, 8);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v___x_3881_, 5);
lean_dec(v_unused_3917_);
v___x_3891_ = v___x_3881_;
v_isShared_3892_ = v_isSharedCheck_3916_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_snapshotTasks_3889_);
lean_inc(v_infoState_3888_);
lean_inc(v_messages_3887_);
lean_inc(v_traceState_3886_);
lean_inc(v_auxDeclNGen_3885_);
lean_inc(v_ngen_3884_);
lean_inc(v_nextMacroScope_3883_);
lean_inc(v_env_3882_);
lean_dec(v___x_3881_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3916_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_inc(v_currNamespace_3880_);
v___x_3893_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3882_, v_ext_3873_, v_b_3874_, v_kind_3875_, v_currNamespace_3880_);
v___x_3894_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 5, v___x_3894_);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_nextMacroScope_3883_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_ngen_3884_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_auxDeclNGen_3885_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v_traceState_3886_);
lean_ctor_set(v_reuseFailAlloc_3915_, 5, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3915_, 6, v_messages_3887_);
lean_ctor_set(v_reuseFailAlloc_3915_, 7, v_infoState_3888_);
lean_ctor_set(v_reuseFailAlloc_3915_, 8, v_snapshotTasks_3889_);
v___x_3896_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v_mctx_3899_; lean_object* v_zetaDeltaFVarIds_3900_; lean_object* v_postponed_3901_; lean_object* v_diag_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3913_; 
v___x_3897_ = lean_st_ref_set(v___y_3878_, v___x_3896_);
v___x_3898_ = lean_st_ref_take(v___y_3876_);
v_mctx_3899_ = lean_ctor_get(v___x_3898_, 0);
v_zetaDeltaFVarIds_3900_ = lean_ctor_get(v___x_3898_, 2);
v_postponed_3901_ = lean_ctor_get(v___x_3898_, 3);
v_diag_3902_ = lean_ctor_get(v___x_3898_, 4);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v___x_3898_, 1);
lean_dec(v_unused_3914_);
v___x_3904_ = v___x_3898_;
v_isShared_3905_ = v_isSharedCheck_3913_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_diag_3902_);
lean_inc(v_postponed_3901_);
lean_inc(v_zetaDeltaFVarIds_3900_);
lean_inc(v_mctx_3899_);
lean_dec(v___x_3898_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3913_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 1, v___x_3906_);
v___x_3908_ = v___x_3904_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_mctx_3899_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_zetaDeltaFVarIds_3900_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_postponed_3901_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_diag_3902_);
v___x_3908_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = lean_st_ref_set(v___y_3876_, v___x_3908_);
v___x_3910_ = lean_box(0);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3918_, lean_object* v_b_3919_, lean_object* v_kind_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v_kind_boxed_3925_; lean_object* v_res_3926_; 
v_kind_boxed_3925_ = lean_unbox(v_kind_3920_);
v_res_3926_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3918_, v_b_3919_, v_kind_boxed_3925_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3927_, lean_object* v_00_u03b2_3928_, lean_object* v_00_u03c3_3929_, lean_object* v_ext_3930_, lean_object* v_b_3931_, uint8_t v_kind_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3930_, v_b_3931_, v_kind_3932_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3939_, lean_object* v_00_u03b2_3940_, lean_object* v_00_u03c3_3941_, lean_object* v_ext_3942_, lean_object* v_b_3943_, lean_object* v_kind_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
uint8_t v_kind_boxed_3950_; lean_object* v_res_3951_; 
v_kind_boxed_3950_ = lean_unbox(v_kind_3944_);
v_res_3951_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3939_, v_00_u03b2_3940_, v_00_u03c3_3941_, v_ext_3942_, v_b_3943_, v_kind_boxed_3950_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___x_3955_; lean_object* v_env_3956_; uint8_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3955_ = lean_st_ref_get(v___y_3953_);
v_env_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc_ref(v_env_3956_);
lean_dec(v___x_3955_);
v___x_3957_ = lean_get_reducibility_status(v_env_3956_, v_declName_3952_);
v___x_3958_ = lean_box(v___x_3957_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3960_, v___y_3961_);
lean_dec(v___y_3961_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3964_, v___y_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_3978_, lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_fileName_3985_; lean_object* v_fileMap_3986_; lean_object* v_options_3987_; lean_object* v_currRecDepth_3988_; lean_object* v_maxRecDepth_3989_; lean_object* v_ref_3990_; lean_object* v_currNamespace_3991_; lean_object* v_openDecls_3992_; lean_object* v_initHeartbeats_3993_; lean_object* v_maxHeartbeats_3994_; lean_object* v_quotContext_3995_; lean_object* v_currMacroScope_3996_; uint8_t v_diag_3997_; lean_object* v_cancelTk_x3f_3998_; uint8_t v_suppressElabErrors_3999_; lean_object* v_inheritedTraceOptions_4000_; lean_object* v_ref_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v_fileName_3985_ = lean_ctor_get(v___y_3982_, 0);
v_fileMap_3986_ = lean_ctor_get(v___y_3982_, 1);
v_options_3987_ = lean_ctor_get(v___y_3982_, 2);
v_currRecDepth_3988_ = lean_ctor_get(v___y_3982_, 3);
v_maxRecDepth_3989_ = lean_ctor_get(v___y_3982_, 4);
v_ref_3990_ = lean_ctor_get(v___y_3982_, 5);
v_currNamespace_3991_ = lean_ctor_get(v___y_3982_, 6);
v_openDecls_3992_ = lean_ctor_get(v___y_3982_, 7);
v_initHeartbeats_3993_ = lean_ctor_get(v___y_3982_, 8);
v_maxHeartbeats_3994_ = lean_ctor_get(v___y_3982_, 9);
v_quotContext_3995_ = lean_ctor_get(v___y_3982_, 10);
v_currMacroScope_3996_ = lean_ctor_get(v___y_3982_, 11);
v_diag_3997_ = lean_ctor_get_uint8(v___y_3982_, sizeof(void*)*14);
v_cancelTk_x3f_3998_ = lean_ctor_get(v___y_3982_, 12);
v_suppressElabErrors_3999_ = lean_ctor_get_uint8(v___y_3982_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4000_ = lean_ctor_get(v___y_3982_, 13);
v_ref_4001_ = l_Lean_replaceRef(v_ref_3978_, v_ref_3990_);
lean_inc_ref(v_inheritedTraceOptions_4000_);
lean_inc(v_cancelTk_x3f_3998_);
lean_inc(v_currMacroScope_3996_);
lean_inc(v_quotContext_3995_);
lean_inc(v_maxHeartbeats_3994_);
lean_inc(v_initHeartbeats_3993_);
lean_inc(v_openDecls_3992_);
lean_inc(v_currNamespace_3991_);
lean_inc(v_maxRecDepth_3989_);
lean_inc(v_currRecDepth_3988_);
lean_inc_ref(v_options_3987_);
lean_inc_ref(v_fileMap_3986_);
lean_inc_ref(v_fileName_3985_);
v___x_4002_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4002_, 0, v_fileName_3985_);
lean_ctor_set(v___x_4002_, 1, v_fileMap_3986_);
lean_ctor_set(v___x_4002_, 2, v_options_3987_);
lean_ctor_set(v___x_4002_, 3, v_currRecDepth_3988_);
lean_ctor_set(v___x_4002_, 4, v_maxRecDepth_3989_);
lean_ctor_set(v___x_4002_, 5, v_ref_4001_);
lean_ctor_set(v___x_4002_, 6, v_currNamespace_3991_);
lean_ctor_set(v___x_4002_, 7, v_openDecls_3992_);
lean_ctor_set(v___x_4002_, 8, v_initHeartbeats_3993_);
lean_ctor_set(v___x_4002_, 9, v_maxHeartbeats_3994_);
lean_ctor_set(v___x_4002_, 10, v_quotContext_3995_);
lean_ctor_set(v___x_4002_, 11, v_currMacroScope_3996_);
lean_ctor_set(v___x_4002_, 12, v_cancelTk_x3f_3998_);
lean_ctor_set(v___x_4002_, 13, v_inheritedTraceOptions_4000_);
lean_ctor_set_uint8(v___x_4002_, sizeof(void*)*14, v_diag_3997_);
lean_ctor_set_uint8(v___x_4002_, sizeof(void*)*14 + 1, v_suppressElabErrors_3999_);
v___x_4003_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3979_, v___y_3980_, v___y_3981_, v___x_4002_, v___y_3983_);
lean_dec_ref_known(v___x_4002_, 14);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4004_, lean_object* v_msg_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4004_, v_msg_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v_ref_4004_);
return v_res_4011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4016_ = lean_unsigned_to_nat(0u);
v___x_4017_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
lean_ctor_set(v___x_4017_, 2, v___x_4016_);
lean_ctor_set(v___x_4017_, 3, v___x_4016_);
lean_ctor_set(v___x_4017_, 4, v___x_4015_);
lean_ctor_set(v___x_4017_, 5, v___x_4015_);
lean_ctor_set(v___x_4017_, 6, v___x_4015_);
lean_ctor_set(v___x_4017_, 7, v___x_4015_);
lean_ctor_set(v___x_4017_, 8, v___x_4015_);
lean_ctor_set(v___x_4017_, 9, v___x_4015_);
return v___x_4017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = lean_unsigned_to_nat(32u);
v___x_4019_ = lean_mk_empty_array_with_capacity(v___x_4018_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4021_ = ((size_t)5ULL);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = lean_unsigned_to_nat(32u);
v___x_4024_ = lean_mk_empty_array_with_capacity(v___x_4023_);
v___x_4025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4026_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
lean_ctor_set(v___x_4026_, 1, v___x_4024_);
lean_ctor_set(v___x_4026_, 2, v___x_4022_);
lean_ctor_set(v___x_4026_, 3, v___x_4022_);
lean_ctor_set_usize(v___x_4026_, 4, v___x_4021_);
return v___x_4026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4027_ = lean_box(1);
v___x_4028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4028_);
lean_ctor_set(v___x_4030_, 2, v___x_4027_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4045_ = l_Lean_stringToMessageData(v___x_4044_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4048_ = l_Lean_stringToMessageData(v___x_4047_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4052_, lean_object* v_declHint_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; lean_object* v_env_4057_; uint8_t v___x_4058_; 
v___x_4056_ = lean_st_ref_get(v___y_4054_);
v_env_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_ref(v_env_4057_);
lean_dec(v___x_4056_);
v___x_4058_ = l_Lean_Name_isAnonymous(v_declHint_4053_);
if (v___x_4058_ == 0)
{
uint8_t v_isExporting_4059_; 
v_isExporting_4059_ = lean_ctor_get_uint8(v_env_4057_, sizeof(void*)*8);
if (v_isExporting_4059_ == 0)
{
lean_object* v___x_4060_; 
lean_dec_ref(v_env_4057_);
lean_dec(v_declHint_4053_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_msg_4052_);
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; uint8_t v___x_4062_; 
lean_inc_ref(v_env_4057_);
v___x_4061_ = l_Lean_Environment_setExporting(v_env_4057_, v___x_4058_);
lean_inc(v_declHint_4053_);
lean_inc_ref(v___x_4061_);
v___x_4062_ = l_Lean_Environment_contains(v___x_4061_, v_declHint_4053_, v_isExporting_4059_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_env_4057_);
lean_dec(v_declHint_4053_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_msg_4052_);
return v___x_4063_;
}
else
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_c_4069_; lean_object* v___x_4070_; 
v___x_4064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4066_ = l_Lean_Options_empty;
v___x_4067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4061_);
lean_ctor_set(v___x_4067_, 1, v___x_4064_);
lean_ctor_set(v___x_4067_, 2, v___x_4065_);
lean_ctor_set(v___x_4067_, 3, v___x_4066_);
lean_inc(v_declHint_4053_);
v___x_4068_ = l_Lean_MessageData_ofConstName(v_declHint_4053_, v___x_4058_);
v_c_4069_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4069_, 0, v___x_4067_);
lean_ctor_set(v_c_4069_, 1, v___x_4068_);
v___x_4070_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4057_, v_declHint_4053_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref(v_env_4057_);
lean_dec(v_declHint_4053_);
v___x_4071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
lean_ctor_set(v___x_4072_, 1, v_c_4069_);
v___x_4073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = l_Lean_MessageData_note(v___x_4074_);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_msg_4052_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
else
{
lean_object* v_val_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4113_; 
v_val_4078_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4080_ = v___x_4070_;
v_isShared_4081_ = v_isSharedCheck_4113_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_val_4078_);
lean_dec(v___x_4070_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4113_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v_mod_4085_; uint8_t v___x_4086_; 
v___x_4082_ = lean_box(0);
v___x_4083_ = l_Lean_Environment_header(v_env_4057_);
lean_dec_ref(v_env_4057_);
v___x_4084_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4083_);
v_mod_4085_ = lean_array_get(v___x_4082_, v___x_4084_, v_val_4078_);
lean_dec(v_val_4078_);
lean_dec_ref(v___x_4084_);
v___x_4086_ = l_Lean_isPrivateName(v_declHint_4053_);
lean_dec(v_declHint_4053_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
lean_ctor_set(v___x_4088_, 1, v_c_4069_);
v___x_4089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_MessageData_ofName(v_mod_4085_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Lean_MessageData_note(v___x_4094_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v_msg_4052_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set_tag(v___x_4080_, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4096_);
v___x_4098_ = v___x_4080_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
else
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v_c_4069_);
v___x_4102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_MessageData_ofName(v_mod_4085_);
v___x_4105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4103_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_MessageData_note(v___x_4107_);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_msg_4052_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set_tag(v___x_4080_, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4109_);
v___x_4111_ = v___x_4080_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4114_; 
lean_dec_ref(v_env_4057_);
lean_dec(v_declHint_4053_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_msg_4052_);
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4115_, lean_object* v_declHint_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4115_, v_declHint_4116_, v___y_4117_);
lean_dec(v___y_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4120_, lean_object* v_declHint_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4137_; 
v___x_4127_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4120_, v_declHint_4121_, v___y_4125_);
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4132_ = l_Lean_unknownIdentifierMessageTag;
v___x_4133_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
lean_ctor_set(v___x_4133_, 1, v_a_4128_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4133_);
v___x_4135_ = v___x_4130_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4138_, lean_object* v_declHint_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4138_, v_declHint_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4146_, lean_object* v_msg_4147_, lean_object* v_declHint_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v_a_4155_; lean_object* v___x_4156_; 
v___x_4154_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4147_, v_declHint_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4146_, v_a_4155_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4157_, lean_object* v_msg_4158_, lean_object* v_declHint_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4157_, v_msg_4158_, v_declHint_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v_ref_4157_);
return v_res_4165_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4168_ = l_Lean_stringToMessageData(v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4169_, lean_object* v_constName_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4176_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4177_ = 0;
lean_inc(v_constName_4170_);
v___x_4178_ = l_Lean_MessageData_ofConstName(v_constName_4170_, v___x_4177_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4176_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4169_, v___x_4181_, v_constName_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4183_, lean_object* v_constName_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4183_, v_constName_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v_ref_4183_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_ref_4197_; lean_object* v___x_4198_; 
v_ref_4197_ = lean_ctor_get(v___y_4194_, 5);
v___x_4198_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4197_, v_constName_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; lean_object* v_env_4213_; uint8_t v___x_4214_; lean_object* v___x_4215_; 
v___x_4212_ = lean_st_ref_get(v___y_4210_);
v_env_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc_ref(v_env_4213_);
lean_dec(v___x_4212_);
v___x_4214_ = 0;
lean_inc(v_constName_4206_);
v___x_4215_ = l_Lean_Environment_find_x3f(v_env_4213_, v_constName_4206_, v___x_4214_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4216_;
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_constName_4206_);
v_val_4217_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4215_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_val_4217_);
lean_dec(v___x_4215_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 0);
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_val_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; lean_object* v_env_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; 
v___x_4238_ = lean_st_ref_get(v___y_4236_);
v_env_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc_ref(v_env_4239_);
lean_dec(v___x_4238_);
v___x_4240_ = 0;
lean_inc(v_constName_4232_);
v___x_4241_ = l_Lean_Environment_findConstVal_x3f(v_env_4239_, v_constName_4232_, v___x_4240_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
return v___x_4242_;
}
else
{
lean_object* v_val_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_constName_4232_);
v_val_4243_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4241_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_val_4243_);
lean_dec(v___x_4241_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 0);
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_val_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
if (lean_obj_tag(v_a_4258_) == 0)
{
lean_object* v___x_4260_; 
v___x_4260_ = l_List_reverse___redArg(v_a_4259_);
return v___x_4260_;
}
else
{
lean_object* v_head_4261_; lean_object* v_tail_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4271_; 
v_head_4261_ = lean_ctor_get(v_a_4258_, 0);
v_tail_4262_ = lean_ctor_get(v_a_4258_, 1);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_a_4258_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4264_ = v_a_4258_;
v_isShared_4265_ = v_isSharedCheck_4271_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_tail_4262_);
lean_inc(v_head_4261_);
lean_dec(v_a_4258_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4271_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4266_ = l_Lean_mkLevelParam(v_head_4261_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 1, v_a_4259_);
lean_ctor_set(v___x_4264_, 0, v___x_4266_);
v___x_4268_ = v___x_4264_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4270_, 1, v_a_4259_);
v___x_4268_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
v_a_4258_ = v_tail_4262_;
v_a_4259_ = v___x_4268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; 
lean_inc(v_constName_4272_);
v___x_4278_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4290_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4281_ = v___x_4278_;
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v_levelParams_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
v_levelParams_4283_ = lean_ctor_get(v_a_4279_, 1);
lean_inc(v_levelParams_4283_);
lean_dec(v_a_4279_);
v___x_4284_ = lean_box(0);
v___x_4285_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4283_, v___x_4284_);
v___x_4286_ = l_Lean_mkConst(v_constName_4272_, v___x_4285_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4286_);
v___x_4288_ = v___x_4281_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v_constName_4272_);
v_a_4291_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4278_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4278_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
return v_res_4305_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4308_ = l_Lean_stringToMessageData(v___x_4307_);
return v___x_4308_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4311_ = l_Lean_stringToMessageData(v___x_4310_);
return v___x_4311_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4314_ = l_Lean_stringToMessageData(v___x_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4315_, uint8_t v_attrKind_4316_, lean_object* v_prio_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v___x_4323_; 
lean_inc(v_declName_4315_);
v___x_4323_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4315_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___x_4397_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
lean_inc(v_declName_4315_);
v___x_4397_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4315_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v___x_4399_ = l_Lean_ConstantInfo_type(v_a_4398_);
v___x_4400_ = l_Lean_Expr_hasSorry(v___x_4399_);
lean_dec_ref(v___x_4399_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; 
lean_inc(v_a_4324_);
v___x_4401_ = l_Lean_Meta_checkNonClassInstance(v_a_4324_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4402_; 
lean_dec_ref_known(v___x_4401_, 1);
v___x_4402_ = l_Lean_Meta_checkImpossibleInstance(v_a_4398_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
lean_dec(v_a_4398_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref_known(v___x_4402_, 1);
v___y_4354_ = v_a_4318_;
v___y_4355_ = v_a_4319_;
v___y_4356_ = v_a_4320_;
v___y_4357_ = v_a_4321_;
goto v___jp_4353_;
}
else
{
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
return v___x_4402_;
}
}
else
{
lean_dec(v_a_4398_);
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
return v___x_4401_;
}
}
else
{
lean_dec(v_a_4398_);
v___y_4354_ = v_a_4318_;
v___y_4355_ = v_a_4319_;
v___y_4356_ = v_a_4320_;
v___y_4357_ = v_a_4321_;
goto v___jp_4353_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
v_a_4403_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4397_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4397_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
v___jp_4325_:
{
lean_object* v___x_4331_; lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4352_; 
lean_inc(v_declName_4315_);
v___x_4331_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4315_, v___y_4330_);
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4334_ = v___x_4331_;
v_isShared_4335_ = v_isSharedCheck_4352_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4331_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4352_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; 
lean_inc(v_a_4324_);
v___x_4336_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4324_, v_a_4332_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4335_ == 0)
{
lean_ctor_set_tag(v___x_4334_, 1);
lean_ctor_set(v___x_4334_, 0, v_declName_4315_);
v___x_4340_ = v___x_4334_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_declName_4315_);
v___x_4340_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4341_, 0, v___y_4326_);
lean_ctor_set(v___x_4341_, 1, v_a_4324_);
lean_ctor_set(v___x_4341_, 2, v_prio_4317_);
lean_ctor_set(v___x_4341_, 3, v___x_4340_);
lean_ctor_set(v___x_4341_, 4, v_a_4337_);
lean_ctor_set_uint8(v___x_4341_, sizeof(void*)*5, v_attrKind_4316_);
v___x_4342_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4338_, v___x_4341_, v_attrKind_4316_, v___y_4328_, v___y_4329_, v___y_4330_);
return v___x_4342_;
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_del_object(v___x_4334_);
lean_dec_ref(v___y_4326_);
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
v_a_4344_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4336_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4336_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
v___jp_4353_:
{
lean_object* v___x_4358_; 
lean_inc(v_a_4324_);
v___x_4358_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4324_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v_a_4361_; uint8_t v___x_4362_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
lean_inc(v_declName_4315_);
v___x_4360_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4315_, v___y_4357_);
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref(v___x_4360_);
v___x_4362_ = lean_unbox(v_a_4361_);
lean_dec(v_a_4361_);
switch(v___x_4362_)
{
case 0:
{
v___y_4326_ = v_a_4359_;
v___y_4327_ = v___y_4354_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
goto v___jp_4325_;
}
case 3:
{
v___y_4326_ = v_a_4359_;
v___y_4327_ = v___y_4354_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
goto v___jp_4325_;
}
default: 
{
lean_object* v___x_4363_; 
lean_inc(v_declName_4315_);
v___x_4363_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4315_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; uint8_t v___x_4365_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = l_Lean_ConstantInfo_isDefinition(v_a_4364_);
lean_dec(v_a_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; lean_object* v_env_4367_; uint8_t v___x_4368_; 
v___x_4366_ = lean_st_ref_get(v___y_4357_);
v_env_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc_ref(v_env_4367_);
lean_dec(v___x_4366_);
lean_inc(v_declName_4315_);
v___x_4368_ = l_Lean_wasOriginallyDefn(v_env_4367_, v_declName_4315_);
if (v___x_4368_ == 0)
{
v___y_4326_ = v_a_4359_;
v___y_4327_ = v___y_4354_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4369_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4315_);
v___x_4370_ = l_Lean_MessageData_ofName(v_declName_4315_);
v___x_4371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4369_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___x_4372_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4373_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_dec_ref_known(v___x_4374_, 1);
v___y_4326_ = v_a_4359_;
v___y_4327_ = v___y_4354_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
goto v___jp_4325_;
}
else
{
lean_dec(v_a_4359_);
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
return v___x_4374_;
}
}
}
else
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4375_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4315_);
v___x_4376_ = l_Lean_MessageData_ofName(v_declName_4315_);
v___x_4377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4375_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
v___x_4378_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4379_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_dec_ref_known(v___x_4380_, 1);
v___y_4326_ = v_a_4359_;
v___y_4327_ = v___y_4354_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
goto v___jp_4325_;
}
else
{
lean_dec(v_a_4359_);
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
return v___x_4380_;
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_a_4359_);
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
v_a_4381_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4363_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4363_);
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
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_a_4324_);
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
v_a_4389_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4358_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4358_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_prio_4317_);
lean_dec(v_declName_4315_);
v_a_4411_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4323_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4323_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4419_, lean_object* v_attrKind_4420_, lean_object* v_prio_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
uint8_t v_attrKind_boxed_4427_; lean_object* v_res_4428_; 
v_attrKind_boxed_4427_ = lean_unbox(v_attrKind_4420_);
v_res_4428_ = l_Lean_Meta_addInstance(v_declName_4419_, v_attrKind_boxed_4427_, v_prio_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4429_, lean_object* v_constName_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4437_, lean_object* v_constName_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4437_, v_constName_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4445_, lean_object* v_ref_4446_, lean_object* v_constName_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4446_, v_constName_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4454_, lean_object* v_ref_4455_, lean_object* v_constName_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4454_, v_ref_4455_, v_constName_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v_ref_4455_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4463_, lean_object* v_ref_4464_, lean_object* v_msg_4465_, lean_object* v_declHint_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4464_, v_msg_4465_, v_declHint_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4473_, lean_object* v_ref_4474_, lean_object* v_msg_4475_, lean_object* v_declHint_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4473_, v_ref_4474_, v_msg_4475_, v_declHint_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v_ref_4474_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4483_, lean_object* v_declHint_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4483_, v_declHint_4484_, v___y_4488_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4491_, lean_object* v_declHint_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4491_, v_declHint_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4499_, lean_object* v_ref_4500_, lean_object* v_msg_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4500_, v_msg_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4508_, lean_object* v_ref_4509_, lean_object* v_msg_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4508_, v_ref_4509_, v_msg_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v_ref_4509_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4517_, uint8_t v_s_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v_env_4523_; lean_object* v_nextMacroScope_4524_; lean_object* v_ngen_4525_; lean_object* v_auxDeclNGen_4526_; lean_object* v_traceState_4527_; lean_object* v_messages_4528_; lean_object* v_infoState_4529_; lean_object* v_snapshotTasks_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4559_; 
v___x_4522_ = lean_st_ref_take(v___y_4520_);
v_env_4523_ = lean_ctor_get(v___x_4522_, 0);
v_nextMacroScope_4524_ = lean_ctor_get(v___x_4522_, 1);
v_ngen_4525_ = lean_ctor_get(v___x_4522_, 2);
v_auxDeclNGen_4526_ = lean_ctor_get(v___x_4522_, 3);
v_traceState_4527_ = lean_ctor_get(v___x_4522_, 4);
v_messages_4528_ = lean_ctor_get(v___x_4522_, 6);
v_infoState_4529_ = lean_ctor_get(v___x_4522_, 7);
v_snapshotTasks_4530_ = lean_ctor_get(v___x_4522_, 8);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; 
v_unused_4560_ = lean_ctor_get(v___x_4522_, 5);
lean_dec(v_unused_4560_);
v___x_4532_ = v___x_4522_;
v_isShared_4533_ = v_isSharedCheck_4559_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_snapshotTasks_4530_);
lean_inc(v_infoState_4529_);
lean_inc(v_messages_4528_);
lean_inc(v_traceState_4527_);
lean_inc(v_auxDeclNGen_4526_);
lean_inc(v_ngen_4525_);
lean_inc(v_nextMacroScope_4524_);
lean_inc(v_env_4523_);
lean_dec(v___x_4522_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4559_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4539_; 
v___x_4534_ = 0;
v___x_4535_ = lean_box(0);
v___x_4536_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4523_, v_declName_4517_, v_s_4518_, v___x_4534_, v___x_4535_);
v___x_4537_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 5, v___x_4537_);
lean_ctor_set(v___x_4532_, 0, v___x_4536_);
v___x_4539_ = v___x_4532_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_nextMacroScope_4524_);
lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_ngen_4525_);
lean_ctor_set(v_reuseFailAlloc_4558_, 3, v_auxDeclNGen_4526_);
lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_traceState_4527_);
lean_ctor_set(v_reuseFailAlloc_4558_, 5, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4558_, 6, v_messages_4528_);
lean_ctor_set(v_reuseFailAlloc_4558_, 7, v_infoState_4529_);
lean_ctor_set(v_reuseFailAlloc_4558_, 8, v_snapshotTasks_4530_);
v___x_4539_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v_mctx_4542_; lean_object* v_zetaDeltaFVarIds_4543_; lean_object* v_postponed_4544_; lean_object* v_diag_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4556_; 
v___x_4540_ = lean_st_ref_set(v___y_4520_, v___x_4539_);
v___x_4541_ = lean_st_ref_take(v___y_4519_);
v_mctx_4542_ = lean_ctor_get(v___x_4541_, 0);
v_zetaDeltaFVarIds_4543_ = lean_ctor_get(v___x_4541_, 2);
v_postponed_4544_ = lean_ctor_get(v___x_4541_, 3);
v_diag_4545_ = lean_ctor_get(v___x_4541_, 4);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; 
v_unused_4557_ = lean_ctor_get(v___x_4541_, 1);
lean_dec(v_unused_4557_);
v___x_4547_ = v___x_4541_;
v_isShared_4548_ = v_isSharedCheck_4556_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_diag_4545_);
lean_inc(v_postponed_4544_);
lean_inc(v_zetaDeltaFVarIds_4543_);
lean_inc(v_mctx_4542_);
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4556_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4549_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 1, v___x_4549_);
v___x_4551_ = v___x_4547_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_mctx_4542_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4555_, 2, v_zetaDeltaFVarIds_4543_);
lean_ctor_set(v_reuseFailAlloc_4555_, 3, v_postponed_4544_);
lean_ctor_set(v_reuseFailAlloc_4555_, 4, v_diag_4545_);
v___x_4551_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = lean_st_ref_set(v___y_4519_, v___x_4551_);
v___x_4553_ = lean_box(0);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
return v___x_4554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4561_, lean_object* v_s_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
uint8_t v_s_boxed_4566_; lean_object* v_res_4567_; 
v_s_boxed_4566_ = lean_unbox(v_s_4562_);
v_res_4567_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4561_, v_s_boxed_4566_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec(v___y_4563_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4568_, uint8_t v_s_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v___x_4575_; 
v___x_4575_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4568_, v_s_4569_, v___y_4571_, v___y_4573_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4576_, lean_object* v_s_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
uint8_t v_s_boxed_4583_; lean_object* v_res_4584_; 
v_s_boxed_4583_ = lean_unbox(v_s_4577_);
v_res_4584_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4576_, v_s_boxed_4583_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4585_, uint8_t v_attrKind_4586_, lean_object* v_prio_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = 3;
lean_inc(v_declName_4585_);
v___x_4594_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4585_, v___x_4593_, v_a_4589_, v_a_4591_);
lean_dec_ref(v___x_4594_);
v___x_4595_ = l_Lean_Meta_addInstance(v_declName_4585_, v_attrKind_4586_, v_prio_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4596_, lean_object* v_attrKind_4597_, lean_object* v_prio_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
uint8_t v_attrKind_boxed_4604_; lean_object* v_res_4605_; 
v_attrKind_boxed_4604_ = lean_unbox(v_attrKind_4597_);
v_res_4605_ = l_Lean_Meta_registerInstance(v_declName_4596_, v_attrKind_boxed_4604_, v_prio_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4606_, lean_object* v_x_4607_){
_start:
{
lean_inc_ref(v_a_4606_);
return v_a_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4608_, lean_object* v_x_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4608_, v_x_4609_);
lean_dec_ref(v_x_4609_);
lean_dec_ref(v_a_4608_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v___x_4615_; lean_object* v_env_4616_; lean_object* v_options_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4615_ = lean_st_ref_get(v___y_4613_);
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4615_);
v_options_4617_ = lean_ctor_get(v___y_4612_, 2);
v___x_4618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4619_ = lean_unsigned_to_nat(32u);
v___x_4620_ = lean_mk_empty_array_with_capacity(v___x_4619_);
lean_dec_ref(v___x_4620_);
v___x_4621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4617_);
v___x_4622_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4622_, 0, v_env_4616_);
lean_ctor_set(v___x_4622_, 1, v___x_4618_);
lean_ctor_set(v___x_4622_, 2, v___x_4621_);
lean_ctor_set(v___x_4622_, 3, v_options_4617_);
v___x_4623_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
lean_ctor_set(v___x_4623_, 1, v_msgData_4611_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_ref_4634_; lean_object* v___x_4635_; lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4644_; 
v_ref_4634_ = lean_ctor_get(v___y_4631_, 5);
v___x_4635_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4630_, v___y_4631_, v___y_4632_);
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4638_ = v___x_4635_;
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4635_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4642_; 
lean_inc(v_ref_4634_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v_ref_4634_);
lean_ctor_set(v___x_4640_, 1, v_a_4636_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set_tag(v___x_4638_, 1);
lean_ctor_set(v___x_4638_, 0, v___x_4640_);
v___x_4642_ = v___x_4638_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
return v_res_4649_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4650_, lean_object* v_i_4651_, lean_object* v_k_4652_){
_start:
{
lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4653_ = lean_array_get_size(v_keys_4650_);
v___x_4654_ = lean_nat_dec_lt(v_i_4651_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_dec(v_i_4651_);
return v___x_4654_;
}
else
{
lean_object* v_k_x27_4655_; uint8_t v___x_4656_; 
v_k_x27_4655_ = lean_array_fget_borrowed(v_keys_4650_, v_i_4651_);
v___x_4656_ = lean_name_eq(v_k_4652_, v_k_x27_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_unsigned_to_nat(1u);
v___x_4658_ = lean_nat_add(v_i_4651_, v___x_4657_);
lean_dec(v_i_4651_);
v_i_4651_ = v___x_4658_;
goto _start;
}
else
{
lean_dec(v_i_4651_);
return v___x_4656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4660_, lean_object* v_i_4661_, lean_object* v_k_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4660_, v_i_4661_, v_k_4662_);
lean_dec(v_k_4662_);
lean_dec_ref(v_keys_4660_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4665_, size_t v_x_4666_, lean_object* v_x_4667_){
_start:
{
if (lean_obj_tag(v_x_4665_) == 0)
{
lean_object* v_es_4668_; lean_object* v___x_4669_; size_t v___x_4670_; size_t v___x_4671_; size_t v___x_4672_; lean_object* v_j_4673_; lean_object* v___x_4674_; 
v_es_4668_ = lean_ctor_get(v_x_4665_, 0);
v___x_4669_ = lean_box(2);
v___x_4670_ = ((size_t)5ULL);
v___x_4671_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4672_ = lean_usize_land(v_x_4666_, v___x_4671_);
v_j_4673_ = lean_usize_to_nat(v___x_4672_);
v___x_4674_ = lean_array_get_borrowed(v___x_4669_, v_es_4668_, v_j_4673_);
lean_dec(v_j_4673_);
switch(lean_obj_tag(v___x_4674_))
{
case 0:
{
lean_object* v_key_4675_; uint8_t v___x_4676_; 
v_key_4675_ = lean_ctor_get(v___x_4674_, 0);
v___x_4676_ = lean_name_eq(v_x_4667_, v_key_4675_);
return v___x_4676_;
}
case 1:
{
lean_object* v_node_4677_; size_t v___x_4678_; 
v_node_4677_ = lean_ctor_get(v___x_4674_, 0);
v___x_4678_ = lean_usize_shift_right(v_x_4666_, v___x_4670_);
v_x_4665_ = v_node_4677_;
v_x_4666_ = v___x_4678_;
goto _start;
}
default: 
{
uint8_t v___x_4680_; 
v___x_4680_ = 0;
return v___x_4680_;
}
}
}
else
{
lean_object* v_ks_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_ks_4681_ = lean_ctor_get(v_x_4665_, 0);
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4681_, v___x_4682_, v_x_4667_);
return v___x_4683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4684_, lean_object* v_x_4685_, lean_object* v_x_4686_){
_start:
{
size_t v_x_2353__boxed_4687_; uint8_t v_res_4688_; lean_object* v_r_4689_; 
v_x_2353__boxed_4687_ = lean_unbox_usize(v_x_4685_);
lean_dec(v_x_4685_);
v_res_4688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4684_, v_x_2353__boxed_4687_, v_x_4686_);
lean_dec(v_x_4686_);
lean_dec_ref(v_x_4684_);
v_r_4689_ = lean_box(v_res_4688_);
return v_r_4689_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4690_, lean_object* v_x_4691_){
_start:
{
uint64_t v___y_4693_; 
if (lean_obj_tag(v_x_4691_) == 0)
{
uint64_t v___x_4696_; 
v___x_4696_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4693_ = v___x_4696_;
goto v___jp_4692_;
}
else
{
uint64_t v_hash_4697_; 
v_hash_4697_ = lean_ctor_get_uint64(v_x_4691_, sizeof(void*)*2);
v___y_4693_ = v_hash_4697_;
goto v___jp_4692_;
}
v___jp_4692_:
{
size_t v___x_4694_; uint8_t v___x_4695_; 
v___x_4694_ = lean_uint64_to_usize(v___y_4693_);
v___x_4695_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4690_, v___x_4694_, v_x_4691_);
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4698_, lean_object* v_x_4699_){
_start:
{
uint8_t v_res_4700_; lean_object* v_r_4701_; 
v_res_4700_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4698_, v_x_4699_);
lean_dec(v_x_4699_);
lean_dec_ref(v_x_4698_);
v_r_4701_ = lean_box(v_res_4700_);
return v_r_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4702_, lean_object* v_declName_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_instanceNames_4710_; uint8_t v___x_4711_; 
v_instanceNames_4710_ = lean_ctor_get(v_d_4702_, 1);
v___x_4711_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4710_, v_declName_4703_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec_ref(v_d_4702_);
v___x_4712_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4713_ = l_Lean_MessageData_ofConstName(v_declName_4703_, v___x_4711_);
v___x_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4714_);
lean_ctor_set(v___x_4716_, 1, v___x_4715_);
v___x_4717_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4716_, v___y_4704_, v___y_4705_);
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4717_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4717_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
else
{
goto v___jp_4707_;
}
v___jp_4707_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = l_Lean_Meta_Instances_eraseCore(v_d_4702_, v_declName_4703_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4726_, lean_object* v_declName_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4726_, v_declName_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4732_, lean_object* v_declName_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v___x_4737_; lean_object* v_env_4738_; lean_object* v___x_4739_; lean_object* v_ext_4740_; lean_object* v_toEnvExtension_4741_; lean_object* v_asyncMode_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4737_ = lean_st_ref_get(v___y_4735_);
v_env_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc_ref(v_env_4738_);
lean_dec(v___x_4737_);
v___x_4739_ = l_Lean_Meta_instanceExtension;
v_ext_4740_ = lean_ctor_get(v___x_4739_, 1);
v_toEnvExtension_4741_ = lean_ctor_get(v_ext_4740_, 0);
v_asyncMode_4742_ = lean_ctor_get(v_toEnvExtension_4741_, 2);
v___x_4743_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4732_, v___x_4739_, v_env_4738_, v_asyncMode_4742_);
v___x_4744_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4743_, v_declName_4733_, v___y_4734_, v___y_4735_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4774_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4747_ = v___x_4744_;
v_isShared_4748_ = v_isSharedCheck_4774_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4744_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4774_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v_env_4750_; lean_object* v_nextMacroScope_4751_; lean_object* v_ngen_4752_; lean_object* v_auxDeclNGen_4753_; lean_object* v_traceState_4754_; lean_object* v_messages_4755_; lean_object* v_infoState_4756_; lean_object* v_snapshotTasks_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4772_; 
v___x_4749_ = lean_st_ref_take(v___y_4735_);
v_env_4750_ = lean_ctor_get(v___x_4749_, 0);
v_nextMacroScope_4751_ = lean_ctor_get(v___x_4749_, 1);
v_ngen_4752_ = lean_ctor_get(v___x_4749_, 2);
v_auxDeclNGen_4753_ = lean_ctor_get(v___x_4749_, 3);
v_traceState_4754_ = lean_ctor_get(v___x_4749_, 4);
v_messages_4755_ = lean_ctor_get(v___x_4749_, 6);
v_infoState_4756_ = lean_ctor_get(v___x_4749_, 7);
v_snapshotTasks_4757_ = lean_ctor_get(v___x_4749_, 8);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v___x_4749_, 5);
lean_dec(v_unused_4773_);
v___x_4759_ = v___x_4749_;
v_isShared_4760_ = v_isSharedCheck_4772_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_snapshotTasks_4757_);
lean_inc(v_infoState_4756_);
lean_inc(v_messages_4755_);
lean_inc(v_traceState_4754_);
lean_inc(v_auxDeclNGen_4753_);
lean_inc(v_ngen_4752_);
lean_inc(v_nextMacroScope_4751_);
lean_inc(v_env_4750_);
lean_dec(v___x_4749_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4772_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___f_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4765_; 
v___f_4761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4761_, 0, v_a_4745_);
v___x_4762_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4739_, v_env_4750_, v___f_4761_);
v___x_4763_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 5, v___x_4763_);
lean_ctor_set(v___x_4759_, 0, v___x_4762_);
v___x_4765_ = v___x_4759_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4762_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_nextMacroScope_4751_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_ngen_4752_);
lean_ctor_set(v_reuseFailAlloc_4771_, 3, v_auxDeclNGen_4753_);
lean_ctor_set(v_reuseFailAlloc_4771_, 4, v_traceState_4754_);
lean_ctor_set(v_reuseFailAlloc_4771_, 5, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4771_, 6, v_messages_4755_);
lean_ctor_set(v_reuseFailAlloc_4771_, 7, v_infoState_4756_);
lean_ctor_set(v_reuseFailAlloc_4771_, 8, v_snapshotTasks_4757_);
v___x_4765_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4766_ = lean_st_ref_set(v___y_4735_, v___x_4765_);
v___x_4767_ = lean_box(0);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 0, v___x_4767_);
v___x_4769_ = v___x_4747_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
v_a_4775_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4744_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4744_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4783_, lean_object* v_declName_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4783_, v_declName_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec_ref(v___x_4783_);
return v_res_4788_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4795_; uint64_t v___x_4796_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4796_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4795_);
return v___x_4796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4797_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4798_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
lean_ctor_set_uint64(v___x_4799_, sizeof(void*)*1, v___x_4797_);
return v___x_4799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4804_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
lean_ctor_set(v___x_4804_, 2, v___x_4803_);
lean_ctor_set(v___x_4804_, 3, v___x_4803_);
lean_ctor_set(v___x_4804_, 4, v___x_4803_);
lean_ctor_set(v___x_4804_, 5, v___x_4803_);
return v___x_4804_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
lean_ctor_set(v___x_4806_, 2, v___x_4805_);
lean_ctor_set(v___x_4806_, 3, v___x_4805_);
lean_ctor_set(v___x_4806_, 4, v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4807_, lean_object* v___x_4808_, lean_object* v_declName_4809_, lean_object* v_stx_4810_, uint8_t v_attrKind_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = lean_unsigned_to_nat(1u);
v___x_4816_ = l_Lean_Syntax_getArg(v_stx_4810_, v___x_4815_);
v___x_4817_ = l_Lean_getAttrParamOptPrio(v___x_4816_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; uint8_t v___x_4819_; uint8_t v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; size_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v___x_4819_ = 0;
v___x_4820_ = 1;
v___x_4821_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4822_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4823_ = lean_unsigned_to_nat(32u);
v___x_4824_ = lean_mk_empty_array_with_capacity(v___x_4823_);
v___x_4825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4826_ = ((size_t)5ULL);
lean_inc_n(v___x_4807_, 6);
v___x_4827_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4827_, 0, v___x_4825_);
lean_ctor_set(v___x_4827_, 1, v___x_4824_);
lean_ctor_set(v___x_4827_, 2, v___x_4807_);
lean_ctor_set(v___x_4827_, 3, v___x_4807_);
lean_ctor_set_usize(v___x_4827_, 4, v___x_4826_);
v___x_4828_ = lean_box(1);
lean_inc_ref(v___x_4827_);
v___x_4829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4822_);
lean_ctor_set(v___x_4829_, 1, v___x_4827_);
lean_ctor_set(v___x_4829_, 2, v___x_4828_);
v___x_4830_ = lean_mk_empty_array_with_capacity(v___x_4807_);
v___x_4831_ = lean_box(0);
lean_inc(v___x_4808_);
v___x_4832_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4832_, 0, v___x_4821_);
lean_ctor_set(v___x_4832_, 1, v___x_4808_);
lean_ctor_set(v___x_4832_, 2, v___x_4829_);
lean_ctor_set(v___x_4832_, 3, v___x_4830_);
lean_ctor_set(v___x_4832_, 4, v___x_4831_);
lean_ctor_set(v___x_4832_, 5, v___x_4807_);
lean_ctor_set(v___x_4832_, 6, v___x_4831_);
lean_ctor_set_uint8(v___x_4832_, sizeof(void*)*7, v___x_4819_);
lean_ctor_set_uint8(v___x_4832_, sizeof(void*)*7 + 1, v___x_4819_);
lean_ctor_set_uint8(v___x_4832_, sizeof(void*)*7 + 2, v___x_4819_);
lean_ctor_set_uint8(v___x_4832_, sizeof(void*)*7 + 3, v___x_4820_);
v___x_4833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4807_);
lean_ctor_set(v___x_4833_, 1, v___x_4807_);
lean_ctor_set(v___x_4833_, 2, v___x_4807_);
lean_ctor_set(v___x_4833_, 3, v___x_4807_);
lean_ctor_set(v___x_4833_, 4, v___x_4822_);
lean_ctor_set(v___x_4833_, 5, v___x_4822_);
lean_ctor_set(v___x_4833_, 6, v___x_4822_);
lean_ctor_set(v___x_4833_, 7, v___x_4822_);
lean_ctor_set(v___x_4833_, 8, v___x_4822_);
lean_ctor_set(v___x_4833_, 9, v___x_4822_);
v___x_4834_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4835_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4833_);
lean_ctor_set(v___x_4836_, 1, v___x_4834_);
lean_ctor_set(v___x_4836_, 2, v___x_4808_);
lean_ctor_set(v___x_4836_, 3, v___x_4827_);
lean_ctor_set(v___x_4836_, 4, v___x_4835_);
v___x_4837_ = lean_st_mk_ref(v___x_4836_);
v___x_4838_ = l_Lean_Meta_addInstance(v_declName_4809_, v_attrKind_4811_, v_a_4818_, v___x_4832_, v___x_4837_, v___y_4812_, v___y_4813_);
lean_dec_ref_known(v___x_4832_, 7);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4847_; 
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v___x_4838_, 0);
lean_dec(v_unused_4848_);
v___x_4840_ = v___x_4838_;
v_isShared_4841_ = v_isSharedCheck_4847_;
goto v_resetjp_4839_;
}
else
{
lean_dec(v___x_4838_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4847_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4845_; 
v___x_4842_ = lean_st_ref_get(v___x_4837_);
lean_dec(v___x_4837_);
lean_dec(v___x_4842_);
v___x_4843_ = lean_box(0);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4843_);
v___x_4845_ = v___x_4840_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
else
{
lean_dec(v___x_4837_);
return v___x_4838_;
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec(v_declName_4809_);
lean_dec(v___x_4808_);
lean_dec(v___x_4807_);
v_a_4849_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4817_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4817_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4857_, lean_object* v___x_4858_, lean_object* v_declName_4859_, lean_object* v_stx_4860_, lean_object* v_attrKind_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
uint8_t v_attrKind_boxed_4865_; lean_object* v_res_4866_; 
v_attrKind_boxed_4865_ = lean_unbox(v_attrKind_4861_);
v_res_4866_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4857_, v___x_4858_, v_declName_4859_, v_stx_4860_, v_attrKind_boxed_4865_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v_stx_4860_);
return v_res_4866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___f_4868_; 
v___x_4867_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4868_, 0, v___x_4867_);
return v___f_4868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4935_; lean_object* v___f_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___f_4935_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4936_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4937_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
lean_ctor_set(v___x_4938_, 1, v___f_4936_);
lean_ctor_set(v___x_4938_, 2, v___f_4935_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4941_ = l_Lean_registerBuiltinAttribute(v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4944_, lean_object* v_x_4945_, lean_object* v_x_4946_){
_start:
{
uint8_t v___x_4947_; 
v___x_4947_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4945_, v_x_4946_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4948_, lean_object* v_x_4949_, lean_object* v_x_4950_){
_start:
{
uint8_t v_res_4951_; lean_object* v_r_4952_; 
v_res_4951_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4948_, v_x_4949_, v_x_4950_);
lean_dec(v_x_4950_);
lean_dec_ref(v_x_4949_);
v_r_4952_ = lean_box(v_res_4951_);
return v_r_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4953_, lean_object* v_msg_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4954_, v___y_4955_, v___y_4956_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4959_, lean_object* v_msg_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4959_, v_msg_4960_, v___y_4961_, v___y_4962_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
return v_res_4964_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4965_, lean_object* v_x_4966_, size_t v_x_4967_, lean_object* v_x_4968_){
_start:
{
uint8_t v___x_4969_; 
v___x_4969_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4966_, v_x_4967_, v_x_4968_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4970_, lean_object* v_x_4971_, lean_object* v_x_4972_, lean_object* v_x_4973_){
_start:
{
size_t v_x_3005__boxed_4974_; uint8_t v_res_4975_; lean_object* v_r_4976_; 
v_x_3005__boxed_4974_ = lean_unbox_usize(v_x_4972_);
lean_dec(v_x_4972_);
v_res_4975_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4970_, v_x_4971_, v_x_3005__boxed_4974_, v_x_4973_);
lean_dec(v_x_4973_);
lean_dec_ref(v_x_4971_);
v_r_4976_ = lean_box(v_res_4975_);
return v_r_4976_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4977_, lean_object* v_keys_4978_, lean_object* v_vals_4979_, lean_object* v_heq_4980_, lean_object* v_i_4981_, lean_object* v_k_4982_){
_start:
{
uint8_t v___x_4983_; 
v___x_4983_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4978_, v_i_4981_, v_k_4982_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4984_, lean_object* v_keys_4985_, lean_object* v_vals_4986_, lean_object* v_heq_4987_, lean_object* v_i_4988_, lean_object* v_k_4989_){
_start:
{
uint8_t v_res_4990_; lean_object* v_r_4991_; 
v_res_4990_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4984_, v_keys_4985_, v_vals_4986_, v_heq_4987_, v_i_4988_, v_k_4989_);
lean_dec(v_k_4989_);
lean_dec_ref(v_vals_4986_);
lean_dec_ref(v_keys_4985_);
v_r_4991_ = lean_box(v_res_4990_);
return v_r_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4995_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4996_ = l_Lean_addBuiltinDocString(v___x_4994_, v___x_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v_env_5002_; lean_object* v___x_5003_; lean_object* v_ext_5004_; lean_object* v_toEnvExtension_5005_; lean_object* v_asyncMode_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v_discrTree_5009_; lean_object* v___x_5010_; 
v___x_5001_ = lean_st_ref_get(v_a_4999_);
v_env_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc_ref(v_env_5002_);
lean_dec(v___x_5001_);
v___x_5003_ = l_Lean_Meta_instanceExtension;
v_ext_5004_ = lean_ctor_get(v___x_5003_, 1);
v_toEnvExtension_5005_ = lean_ctor_get(v_ext_5004_, 0);
v_asyncMode_5006_ = lean_ctor_get(v_toEnvExtension_5005_, 2);
v___x_5007_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5008_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5007_, v___x_5003_, v_env_5002_, v_asyncMode_5006_);
v_discrTree_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc_ref(v_discrTree_5009_);
lean_dec(v___x_5008_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_discrTree_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5011_);
lean_dec(v_a_5011_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5015_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5018_, v_a_5019_);
lean_dec(v_a_5019_);
lean_dec_ref(v_a_5018_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5022_){
_start:
{
lean_object* v___x_5024_; lean_object* v_env_5025_; lean_object* v___x_5026_; lean_object* v_ext_5027_; lean_object* v_toEnvExtension_5028_; lean_object* v_asyncMode_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v_erased_5032_; lean_object* v___x_5033_; 
v___x_5024_ = lean_st_ref_get(v_a_5022_);
v_env_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc_ref(v_env_5025_);
lean_dec(v___x_5024_);
v___x_5026_ = l_Lean_Meta_instanceExtension;
v_ext_5027_ = lean_ctor_get(v___x_5026_, 1);
v_toEnvExtension_5028_ = lean_ctor_get(v_ext_5027_, 0);
v_asyncMode_5029_ = lean_ctor_get(v_toEnvExtension_5028_, 2);
v___x_5030_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5031_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5030_, v___x_5026_, v_env_5025_, v_asyncMode_5029_);
v_erased_5032_ = lean_ctor_get(v___x_5031_, 2);
lean_inc_ref(v_erased_5032_);
lean_dec(v___x_5031_);
v___x_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5033_, 0, v_erased_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5034_, lean_object* v_a_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5034_);
lean_dec(v_a_5034_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v___x_5040_; 
v___x_5040_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5038_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Meta_getErasedInstances(v_a_5041_, v_a_5042_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
return v_res_5044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5045_, lean_object* v_declName_5046_){
_start:
{
lean_object* v___x_5047_; lean_object* v_ext_5048_; lean_object* v_toEnvExtension_5049_; lean_object* v_asyncMode_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v_instanceNames_5053_; uint8_t v___x_5054_; 
v___x_5047_ = l_Lean_Meta_instanceExtension;
v_ext_5048_ = lean_ctor_get(v___x_5047_, 1);
v_toEnvExtension_5049_ = lean_ctor_get(v_ext_5048_, 0);
v_asyncMode_5050_ = lean_ctor_get(v_toEnvExtension_5049_, 2);
v___x_5051_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5052_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5051_, v___x_5047_, v_env_5045_, v_asyncMode_5050_);
v_instanceNames_5053_ = lean_ctor_get(v___x_5052_, 1);
lean_inc_ref(v_instanceNames_5053_);
lean_dec(v___x_5052_);
v___x_5054_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5053_, v_declName_5046_);
lean_dec_ref(v_instanceNames_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5055_, lean_object* v_declName_5056_){
_start:
{
uint8_t v_res_5057_; lean_object* v_r_5058_; 
v_res_5057_ = l_Lean_Meta_isInstanceCore(v_env_5055_, v_declName_5056_);
lean_dec(v_declName_5056_);
v_r_5058_ = lean_box(v_res_5057_);
return v_r_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v___x_5062_; lean_object* v_env_5063_; uint8_t v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5062_ = lean_st_ref_get(v_a_5060_);
v_env_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc_ref(v_env_5063_);
lean_dec(v___x_5062_);
v___x_5064_ = l_Lean_Meta_isInstanceCore(v_env_5063_, v_declName_5059_);
v___x_5065_ = lean_box(v___x_5064_);
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_Meta_isInstance___redArg(v_declName_5067_, v_a_5068_);
lean_dec(v_a_5068_);
lean_dec(v_declName_5067_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Meta_isInstance___redArg(v_declName_5071_, v_a_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Meta_isInstance(v_declName_5076_, v_a_5077_, v_a_5078_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_declName_5076_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5081_, lean_object* v_vals_5082_, lean_object* v_i_5083_, lean_object* v_k_5084_){
_start:
{
lean_object* v___x_5085_; uint8_t v___x_5086_; 
v___x_5085_ = lean_array_get_size(v_keys_5081_);
v___x_5086_ = lean_nat_dec_lt(v_i_5083_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; 
lean_dec(v_i_5083_);
v___x_5087_ = lean_box(0);
return v___x_5087_;
}
else
{
lean_object* v_k_x27_5088_; uint8_t v___x_5089_; 
v_k_x27_5088_ = lean_array_fget_borrowed(v_keys_5081_, v_i_5083_);
v___x_5089_ = lean_name_eq(v_k_5084_, v_k_x27_5088_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = lean_unsigned_to_nat(1u);
v___x_5091_ = lean_nat_add(v_i_5083_, v___x_5090_);
lean_dec(v_i_5083_);
v_i_5083_ = v___x_5091_;
goto _start;
}
else
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_array_fget_borrowed(v_vals_5082_, v_i_5083_);
lean_dec(v_i_5083_);
lean_inc(v___x_5093_);
v___x_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
return v___x_5094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5095_, lean_object* v_vals_5096_, lean_object* v_i_5097_, lean_object* v_k_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5095_, v_vals_5096_, v_i_5097_, v_k_5098_);
lean_dec(v_k_5098_);
lean_dec_ref(v_vals_5096_);
lean_dec_ref(v_keys_5095_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5100_, size_t v_x_5101_, lean_object* v_x_5102_){
_start:
{
if (lean_obj_tag(v_x_5100_) == 0)
{
lean_object* v_es_5103_; lean_object* v___x_5104_; size_t v___x_5105_; size_t v___x_5106_; size_t v___x_5107_; lean_object* v_j_5108_; lean_object* v___x_5109_; 
v_es_5103_ = lean_ctor_get(v_x_5100_, 0);
v___x_5104_ = lean_box(2);
v___x_5105_ = ((size_t)5ULL);
v___x_5106_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_5107_ = lean_usize_land(v_x_5101_, v___x_5106_);
v_j_5108_ = lean_usize_to_nat(v___x_5107_);
v___x_5109_ = lean_array_get_borrowed(v___x_5104_, v_es_5103_, v_j_5108_);
lean_dec(v_j_5108_);
switch(lean_obj_tag(v___x_5109_))
{
case 0:
{
lean_object* v_key_5110_; lean_object* v_val_5111_; uint8_t v___x_5112_; 
v_key_5110_ = lean_ctor_get(v___x_5109_, 0);
v_val_5111_ = lean_ctor_get(v___x_5109_, 1);
v___x_5112_ = lean_name_eq(v_x_5102_, v_key_5110_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_box(0);
return v___x_5113_;
}
else
{
lean_object* v___x_5114_; 
lean_inc(v_val_5111_);
v___x_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5114_, 0, v_val_5111_);
return v___x_5114_;
}
}
case 1:
{
lean_object* v_node_5115_; size_t v___x_5116_; 
v_node_5115_ = lean_ctor_get(v___x_5109_, 0);
v___x_5116_ = lean_usize_shift_right(v_x_5101_, v___x_5105_);
v_x_5100_ = v_node_5115_;
v_x_5101_ = v___x_5116_;
goto _start;
}
default: 
{
lean_object* v___x_5118_; 
v___x_5118_ = lean_box(0);
return v___x_5118_;
}
}
}
else
{
lean_object* v_ks_5119_; lean_object* v_vs_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_ks_5119_ = lean_ctor_get(v_x_5100_, 0);
v_vs_5120_ = lean_ctor_get(v_x_5100_, 1);
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5119_, v_vs_5120_, v___x_5121_, v_x_5102_);
return v___x_5122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5123_, lean_object* v_x_5124_, lean_object* v_x_5125_){
_start:
{
size_t v_x_489__boxed_5126_; lean_object* v_res_5127_; 
v_x_489__boxed_5126_ = lean_unbox_usize(v_x_5124_);
lean_dec(v_x_5124_);
v_res_5127_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5123_, v_x_489__boxed_5126_, v_x_5125_);
lean_dec(v_x_5125_);
lean_dec_ref(v_x_5123_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5128_, lean_object* v_x_5129_){
_start:
{
uint64_t v___y_5131_; 
if (lean_obj_tag(v_x_5129_) == 0)
{
uint64_t v___x_5134_; 
v___x_5134_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_5131_ = v___x_5134_;
goto v___jp_5130_;
}
else
{
uint64_t v_hash_5135_; 
v_hash_5135_ = lean_ctor_get_uint64(v_x_5129_, sizeof(void*)*2);
v___y_5131_ = v_hash_5135_;
goto v___jp_5130_;
}
v___jp_5130_:
{
size_t v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = lean_uint64_to_usize(v___y_5131_);
v___x_5133_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5128_, v___x_5132_, v_x_5129_);
return v___x_5133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5136_, lean_object* v_x_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5136_, v_x_5137_);
lean_dec(v_x_5137_);
lean_dec_ref(v_x_5136_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v___x_5142_; lean_object* v_env_5143_; lean_object* v___x_5144_; lean_object* v_ext_5145_; lean_object* v_toEnvExtension_5146_; lean_object* v_asyncMode_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v_instanceNames_5150_; lean_object* v___x_5151_; 
v___x_5142_ = lean_st_ref_get(v_a_5140_);
v_env_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc_ref(v_env_5143_);
lean_dec(v___x_5142_);
v___x_5144_ = l_Lean_Meta_instanceExtension;
v_ext_5145_ = lean_ctor_get(v___x_5144_, 1);
v_toEnvExtension_5146_ = lean_ctor_get(v_ext_5145_, 0);
v_asyncMode_5147_ = lean_ctor_get(v_toEnvExtension_5146_, 2);
v___x_5148_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5149_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5148_, v___x_5144_, v_env_5143_, v_asyncMode_5147_);
v_instanceNames_5150_ = lean_ctor_get(v___x_5149_, 1);
lean_inc_ref(v_instanceNames_5150_);
lean_dec(v___x_5149_);
v___x_5151_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5150_, v_declName_5139_);
lean_dec_ref(v_instanceNames_5150_);
if (lean_obj_tag(v___x_5151_) == 1)
{
lean_object* v_val_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5161_; 
v_val_5152_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5154_ = v___x_5151_;
v_isShared_5155_ = v_isSharedCheck_5161_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_val_5152_);
lean_dec(v___x_5151_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5161_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v_priority_5156_; lean_object* v___x_5158_; 
v_priority_5156_ = lean_ctor_get(v_val_5152_, 2);
lean_inc(v_priority_5156_);
lean_dec(v_val_5152_);
if (v_isShared_5155_ == 0)
{
lean_ctor_set(v___x_5154_, 0, v_priority_5156_);
v___x_5158_ = v___x_5154_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_priority_5156_);
v___x_5158_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5158_);
return v___x_5159_;
}
}
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_dec(v___x_5151_);
v___x_5162_ = lean_box(0);
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
return v___x_5163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5164_, v_a_5165_);
lean_dec(v_a_5165_);
lean_dec(v_declName_5164_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_){
_start:
{
lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5168_, v_a_5170_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5173_, v_a_5174_, v_a_5175_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_declName_5173_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5178_, lean_object* v_x_5179_, lean_object* v_x_5180_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5179_, v_x_5180_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5182_, lean_object* v_x_5183_, lean_object* v_x_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5182_, v_x_5183_, v_x_5184_);
lean_dec(v_x_5184_);
lean_dec_ref(v_x_5183_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5186_, lean_object* v_x_5187_, size_t v_x_5188_, lean_object* v_x_5189_){
_start:
{
lean_object* v___x_5190_; 
v___x_5190_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5187_, v_x_5188_, v_x_5189_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5191_, lean_object* v_x_5192_, lean_object* v_x_5193_, lean_object* v_x_5194_){
_start:
{
size_t v_x_605__boxed_5195_; lean_object* v_res_5196_; 
v_x_605__boxed_5195_ = lean_unbox_usize(v_x_5193_);
lean_dec(v_x_5193_);
v_res_5196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5191_, v_x_5192_, v_x_605__boxed_5195_, v_x_5194_);
lean_dec(v_x_5194_);
lean_dec_ref(v_x_5192_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5197_, lean_object* v_keys_5198_, lean_object* v_vals_5199_, lean_object* v_heq_5200_, lean_object* v_i_5201_, lean_object* v_k_5202_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5198_, v_vals_5199_, v_i_5201_, v_k_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5204_, lean_object* v_keys_5205_, lean_object* v_vals_5206_, lean_object* v_heq_5207_, lean_object* v_i_5208_, lean_object* v_k_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5204_, v_keys_5205_, v_vals_5206_, v_heq_5207_, v_i_5208_, v_k_5209_);
lean_dec(v_k_5209_);
lean_dec_ref(v_vals_5206_);
lean_dec_ref(v_keys_5205_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5211_, lean_object* v_a_5212_){
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
lean_object* v_val_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5234_; 
v_val_5224_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5226_ = v___x_5223_;
v_isShared_5227_ = v_isSharedCheck_5234_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_val_5224_);
lean_dec(v___x_5223_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5234_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
uint8_t v_attrKind_5228_; lean_object* v___x_5229_; lean_object* v___x_5231_; 
v_attrKind_5228_ = lean_ctor_get_uint8(v_val_5224_, sizeof(void*)*5);
lean_dec(v_val_5224_);
v___x_5229_ = lean_box(v_attrKind_5228_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 0, v___x_5229_);
v___x_5231_ = v___x_5226_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5229_);
v___x_5231_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5232_; 
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
return v___x_5232_;
}
}
}
else
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
lean_dec(v___x_5223_);
v___x_5235_ = lean_box(0);
v___x_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
return v___x_5236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5237_, v_a_5238_);
lean_dec(v_a_5238_);
lean_dec(v_declName_5237_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5241_, v_a_5243_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5246_, v_a_5247_, v_a_5248_);
lean_dec(v_a_5248_);
lean_dec_ref(v_a_5247_);
lean_dec(v_declName_5246_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5255_, lean_object* v_v_5256_, lean_object* v_t_5257_){
_start:
{
if (lean_obj_tag(v_t_5257_) == 0)
{
lean_object* v_size_5258_; lean_object* v_k_5259_; lean_object* v_v_5260_; lean_object* v_l_5261_; lean_object* v_r_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5543_; 
v_size_5258_ = lean_ctor_get(v_t_5257_, 0);
v_k_5259_ = lean_ctor_get(v_t_5257_, 1);
v_v_5260_ = lean_ctor_get(v_t_5257_, 2);
v_l_5261_ = lean_ctor_get(v_t_5257_, 3);
v_r_5262_ = lean_ctor_get(v_t_5257_, 4);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_t_5257_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5264_ = v_t_5257_;
v_isShared_5265_ = v_isSharedCheck_5543_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_r_5262_);
lean_inc(v_l_5261_);
lean_inc(v_v_5260_);
lean_inc(v_k_5259_);
lean_inc(v_size_5258_);
lean_dec(v_t_5257_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5543_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
uint8_t v___x_5266_; 
v___x_5266_ = lean_nat_dec_lt(v_k_5259_, v_k_5255_);
if (v___x_5266_ == 0)
{
uint8_t v___x_5267_; 
v___x_5267_ = lean_nat_dec_eq(v_k_5259_, v_k_5255_);
if (v___x_5267_ == 0)
{
lean_object* v_impl_5268_; lean_object* v___x_5269_; 
lean_dec(v_size_5258_);
v_impl_5268_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5255_, v_v_5256_, v_r_5262_);
v___x_5269_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5261_) == 0)
{
lean_object* v_size_5270_; lean_object* v_size_5271_; lean_object* v_k_5272_; lean_object* v_v_5273_; lean_object* v_l_5274_; lean_object* v_r_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; 
v_size_5270_ = lean_ctor_get(v_l_5261_, 0);
v_size_5271_ = lean_ctor_get(v_impl_5268_, 0);
lean_inc(v_size_5271_);
v_k_5272_ = lean_ctor_get(v_impl_5268_, 1);
lean_inc(v_k_5272_);
v_v_5273_ = lean_ctor_get(v_impl_5268_, 2);
lean_inc(v_v_5273_);
v_l_5274_ = lean_ctor_get(v_impl_5268_, 3);
lean_inc(v_l_5274_);
v_r_5275_ = lean_ctor_get(v_impl_5268_, 4);
lean_inc(v_r_5275_);
v___x_5276_ = lean_unsigned_to_nat(3u);
v___x_5277_ = lean_nat_mul(v___x_5276_, v_size_5270_);
v___x_5278_ = lean_nat_dec_lt(v___x_5277_, v_size_5271_);
lean_dec(v___x_5277_);
if (v___x_5278_ == 0)
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5282_; 
lean_dec(v_r_5275_);
lean_dec(v_l_5274_);
lean_dec(v_v_5273_);
lean_dec(v_k_5272_);
v___x_5279_ = lean_nat_add(v___x_5269_, v_size_5270_);
v___x_5280_ = lean_nat_add(v___x_5279_, v_size_5271_);
lean_dec(v_size_5271_);
lean_dec(v___x_5279_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_impl_5268_);
lean_ctor_set(v___x_5264_, 0, v___x_5280_);
v___x_5282_ = v___x_5264_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
lean_ctor_set(v_reuseFailAlloc_5283_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5283_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5283_, 3, v_l_5261_);
lean_ctor_set(v_reuseFailAlloc_5283_, 4, v_impl_5268_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
else
{
lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5347_; 
v_isSharedCheck_5347_ = !lean_is_exclusive(v_impl_5268_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; lean_object* v_unused_5349_; lean_object* v_unused_5350_; lean_object* v_unused_5351_; lean_object* v_unused_5352_; 
v_unused_5348_ = lean_ctor_get(v_impl_5268_, 4);
lean_dec(v_unused_5348_);
v_unused_5349_ = lean_ctor_get(v_impl_5268_, 3);
lean_dec(v_unused_5349_);
v_unused_5350_ = lean_ctor_get(v_impl_5268_, 2);
lean_dec(v_unused_5350_);
v_unused_5351_ = lean_ctor_get(v_impl_5268_, 1);
lean_dec(v_unused_5351_);
v_unused_5352_ = lean_ctor_get(v_impl_5268_, 0);
lean_dec(v_unused_5352_);
v___x_5285_ = v_impl_5268_;
v_isShared_5286_ = v_isSharedCheck_5347_;
goto v_resetjp_5284_;
}
else
{
lean_dec(v_impl_5268_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5347_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v_size_5287_; lean_object* v_k_5288_; lean_object* v_v_5289_; lean_object* v_l_5290_; lean_object* v_r_5291_; lean_object* v_size_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v_size_5287_ = lean_ctor_get(v_l_5274_, 0);
v_k_5288_ = lean_ctor_get(v_l_5274_, 1);
v_v_5289_ = lean_ctor_get(v_l_5274_, 2);
v_l_5290_ = lean_ctor_get(v_l_5274_, 3);
v_r_5291_ = lean_ctor_get(v_l_5274_, 4);
v_size_5292_ = lean_ctor_get(v_r_5275_, 0);
v___x_5293_ = lean_unsigned_to_nat(2u);
v___x_5294_ = lean_nat_mul(v___x_5293_, v_size_5292_);
v___x_5295_ = lean_nat_dec_lt(v_size_5287_, v___x_5294_);
lean_dec(v___x_5294_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5323_; 
lean_inc(v_r_5291_);
lean_inc(v_l_5290_);
lean_inc(v_v_5289_);
lean_inc(v_k_5288_);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_l_5274_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; lean_object* v_unused_5325_; lean_object* v_unused_5326_; lean_object* v_unused_5327_; lean_object* v_unused_5328_; 
v_unused_5324_ = lean_ctor_get(v_l_5274_, 4);
lean_dec(v_unused_5324_);
v_unused_5325_ = lean_ctor_get(v_l_5274_, 3);
lean_dec(v_unused_5325_);
v_unused_5326_ = lean_ctor_get(v_l_5274_, 2);
lean_dec(v_unused_5326_);
v_unused_5327_ = lean_ctor_get(v_l_5274_, 1);
lean_dec(v_unused_5327_);
v_unused_5328_ = lean_ctor_get(v_l_5274_, 0);
lean_dec(v_unused_5328_);
v___x_5297_ = v_l_5274_;
v_isShared_5298_ = v_isSharedCheck_5323_;
goto v_resetjp_5296_;
}
else
{
lean_dec(v_l_5274_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5323_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___y_5302_; lean_object* v___y_5303_; lean_object* v___y_5304_; lean_object* v___y_5313_; 
v___x_5299_ = lean_nat_add(v___x_5269_, v_size_5270_);
v___x_5300_ = lean_nat_add(v___x_5299_, v_size_5271_);
lean_dec(v_size_5271_);
if (lean_obj_tag(v_l_5290_) == 0)
{
lean_object* v_size_5321_; 
v_size_5321_ = lean_ctor_get(v_l_5290_, 0);
lean_inc(v_size_5321_);
v___y_5313_ = v_size_5321_;
goto v___jp_5312_;
}
else
{
lean_object* v___x_5322_; 
v___x_5322_ = lean_unsigned_to_nat(0u);
v___y_5313_ = v___x_5322_;
goto v___jp_5312_;
}
v___jp_5301_:
{
lean_object* v___x_5305_; lean_object* v___x_5307_; 
v___x_5305_ = lean_nat_add(v___y_5302_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec(v___y_5302_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 4, v_r_5275_);
lean_ctor_set(v___x_5297_, 3, v_r_5291_);
lean_ctor_set(v___x_5297_, 2, v_v_5273_);
lean_ctor_set(v___x_5297_, 1, v_k_5272_);
lean_ctor_set(v___x_5297_, 0, v___x_5305_);
v___x_5307_ = v___x_5297_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v___x_5305_);
lean_ctor_set(v_reuseFailAlloc_5311_, 1, v_k_5272_);
lean_ctor_set(v_reuseFailAlloc_5311_, 2, v_v_5273_);
lean_ctor_set(v_reuseFailAlloc_5311_, 3, v_r_5291_);
lean_ctor_set(v_reuseFailAlloc_5311_, 4, v_r_5275_);
v___x_5307_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
lean_object* v___x_5309_; 
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 4, v___x_5307_);
lean_ctor_set(v___x_5285_, 3, v___y_5303_);
lean_ctor_set(v___x_5285_, 2, v_v_5289_);
lean_ctor_set(v___x_5285_, 1, v_k_5288_);
lean_ctor_set(v___x_5285_, 0, v___x_5300_);
v___x_5309_ = v___x_5285_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5300_);
lean_ctor_set(v_reuseFailAlloc_5310_, 1, v_k_5288_);
lean_ctor_set(v_reuseFailAlloc_5310_, 2, v_v_5289_);
lean_ctor_set(v_reuseFailAlloc_5310_, 3, v___y_5303_);
lean_ctor_set(v_reuseFailAlloc_5310_, 4, v___x_5307_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
v___jp_5312_:
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
v___x_5314_ = lean_nat_add(v___x_5299_, v___y_5313_);
lean_dec(v___y_5313_);
lean_dec(v___x_5299_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_l_5290_);
lean_ctor_set(v___x_5264_, 0, v___x_5314_);
v___x_5316_ = v___x_5264_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5314_);
lean_ctor_set(v_reuseFailAlloc_5320_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5320_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5320_, 3, v_l_5261_);
lean_ctor_set(v_reuseFailAlloc_5320_, 4, v_l_5290_);
v___x_5316_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5317_; 
v___x_5317_ = lean_nat_add(v___x_5269_, v_size_5292_);
if (lean_obj_tag(v_r_5291_) == 0)
{
lean_object* v_size_5318_; 
v_size_5318_ = lean_ctor_get(v_r_5291_, 0);
lean_inc(v_size_5318_);
v___y_5302_ = v___x_5317_;
v___y_5303_ = v___x_5316_;
v___y_5304_ = v_size_5318_;
goto v___jp_5301_;
}
else
{
lean_object* v___x_5319_; 
v___x_5319_ = lean_unsigned_to_nat(0u);
v___y_5302_ = v___x_5317_;
v___y_5303_ = v___x_5316_;
v___y_5304_ = v___x_5319_;
goto v___jp_5301_;
}
}
}
}
}
else
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; 
lean_del_object(v___x_5264_);
v___x_5329_ = lean_nat_add(v___x_5269_, v_size_5270_);
v___x_5330_ = lean_nat_add(v___x_5329_, v_size_5271_);
lean_dec(v_size_5271_);
v___x_5331_ = lean_nat_add(v___x_5329_, v_size_5287_);
lean_dec(v___x_5329_);
lean_inc_ref(v_l_5261_);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 4, v_l_5274_);
lean_ctor_set(v___x_5285_, 3, v_l_5261_);
lean_ctor_set(v___x_5285_, 2, v_v_5260_);
lean_ctor_set(v___x_5285_, 1, v_k_5259_);
lean_ctor_set(v___x_5285_, 0, v___x_5331_);
v___x_5333_ = v___x_5285_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5346_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5346_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5346_, 3, v_l_5261_);
lean_ctor_set(v_reuseFailAlloc_5346_, 4, v_l_5274_);
v___x_5333_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
v_isSharedCheck_5340_ = !lean_is_exclusive(v_l_5261_);
if (v_isSharedCheck_5340_ == 0)
{
lean_object* v_unused_5341_; lean_object* v_unused_5342_; lean_object* v_unused_5343_; lean_object* v_unused_5344_; lean_object* v_unused_5345_; 
v_unused_5341_ = lean_ctor_get(v_l_5261_, 4);
lean_dec(v_unused_5341_);
v_unused_5342_ = lean_ctor_get(v_l_5261_, 3);
lean_dec(v_unused_5342_);
v_unused_5343_ = lean_ctor_get(v_l_5261_, 2);
lean_dec(v_unused_5343_);
v_unused_5344_ = lean_ctor_get(v_l_5261_, 1);
lean_dec(v_unused_5344_);
v_unused_5345_ = lean_ctor_get(v_l_5261_, 0);
lean_dec(v_unused_5345_);
v___x_5335_ = v_l_5261_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_dec(v_l_5261_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 4, v_r_5275_);
lean_ctor_set(v___x_5335_, 3, v___x_5333_);
lean_ctor_set(v___x_5335_, 2, v_v_5273_);
lean_ctor_set(v___x_5335_, 1, v_k_5272_);
lean_ctor_set(v___x_5335_, 0, v___x_5330_);
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5339_, 1, v_k_5272_);
lean_ctor_set(v_reuseFailAlloc_5339_, 2, v_v_5273_);
lean_ctor_set(v_reuseFailAlloc_5339_, 3, v___x_5333_);
lean_ctor_set(v_reuseFailAlloc_5339_, 4, v_r_5275_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5353_; 
v_l_5353_ = lean_ctor_get(v_impl_5268_, 3);
lean_inc(v_l_5353_);
if (lean_obj_tag(v_l_5353_) == 0)
{
lean_object* v_r_5354_; lean_object* v_k_5355_; lean_object* v_v_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5379_; 
v_r_5354_ = lean_ctor_get(v_impl_5268_, 4);
v_k_5355_ = lean_ctor_get(v_impl_5268_, 1);
v_v_5356_ = lean_ctor_get(v_impl_5268_, 2);
v_isSharedCheck_5379_ = !lean_is_exclusive(v_impl_5268_);
if (v_isSharedCheck_5379_ == 0)
{
lean_object* v_unused_5380_; lean_object* v_unused_5381_; 
v_unused_5380_ = lean_ctor_get(v_impl_5268_, 3);
lean_dec(v_unused_5380_);
v_unused_5381_ = lean_ctor_get(v_impl_5268_, 0);
lean_dec(v_unused_5381_);
v___x_5358_ = v_impl_5268_;
v_isShared_5359_ = v_isSharedCheck_5379_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_r_5354_);
lean_inc(v_v_5356_);
lean_inc(v_k_5355_);
lean_dec(v_impl_5268_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5379_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v_k_5360_; lean_object* v_v_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5375_; 
v_k_5360_ = lean_ctor_get(v_l_5353_, 1);
v_v_5361_ = lean_ctor_get(v_l_5353_, 2);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_l_5353_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; lean_object* v_unused_5377_; lean_object* v_unused_5378_; 
v_unused_5376_ = lean_ctor_get(v_l_5353_, 4);
lean_dec(v_unused_5376_);
v_unused_5377_ = lean_ctor_get(v_l_5353_, 3);
lean_dec(v_unused_5377_);
v_unused_5378_ = lean_ctor_get(v_l_5353_, 0);
lean_dec(v_unused_5378_);
v___x_5363_ = v_l_5353_;
v_isShared_5364_ = v_isSharedCheck_5375_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_v_5361_);
lean_inc(v_k_5360_);
lean_dec(v_l_5353_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5375_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
v___x_5365_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5354_, 2);
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 4, v_r_5354_);
lean_ctor_set(v___x_5363_, 3, v_r_5354_);
lean_ctor_set(v___x_5363_, 2, v_v_5260_);
lean_ctor_set(v___x_5363_, 1, v_k_5259_);
lean_ctor_set(v___x_5363_, 0, v___x_5269_);
v___x_5367_ = v___x_5363_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5374_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5374_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5374_, 3, v_r_5354_);
lean_ctor_set(v_reuseFailAlloc_5374_, 4, v_r_5354_);
v___x_5367_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5369_; 
lean_inc(v_r_5354_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 3, v_r_5354_);
lean_ctor_set(v___x_5358_, 0, v___x_5269_);
v___x_5369_ = v___x_5358_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_k_5355_);
lean_ctor_set(v_reuseFailAlloc_5373_, 2, v_v_5356_);
lean_ctor_set(v_reuseFailAlloc_5373_, 3, v_r_5354_);
lean_ctor_set(v_reuseFailAlloc_5373_, 4, v_r_5354_);
v___x_5369_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
lean_object* v___x_5371_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v___x_5369_);
lean_ctor_set(v___x_5264_, 3, v___x_5367_);
lean_ctor_set(v___x_5264_, 2, v_v_5361_);
lean_ctor_set(v___x_5264_, 1, v_k_5360_);
lean_ctor_set(v___x_5264_, 0, v___x_5365_);
v___x_5371_ = v___x_5264_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5372_, 3, v___x_5367_);
lean_ctor_set(v_reuseFailAlloc_5372_, 4, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
}
else
{
lean_object* v_r_5382_; 
v_r_5382_ = lean_ctor_get(v_impl_5268_, 4);
lean_inc(v_r_5382_);
if (lean_obj_tag(v_r_5382_) == 0)
{
lean_object* v_k_5383_; lean_object* v_v_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5395_; 
v_k_5383_ = lean_ctor_get(v_impl_5268_, 1);
v_v_5384_ = lean_ctor_get(v_impl_5268_, 2);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_impl_5268_);
if (v_isSharedCheck_5395_ == 0)
{
lean_object* v_unused_5396_; lean_object* v_unused_5397_; lean_object* v_unused_5398_; 
v_unused_5396_ = lean_ctor_get(v_impl_5268_, 4);
lean_dec(v_unused_5396_);
v_unused_5397_ = lean_ctor_get(v_impl_5268_, 3);
lean_dec(v_unused_5397_);
v_unused_5398_ = lean_ctor_get(v_impl_5268_, 0);
lean_dec(v_unused_5398_);
v___x_5386_ = v_impl_5268_;
v_isShared_5387_ = v_isSharedCheck_5395_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_v_5384_);
lean_inc(v_k_5383_);
lean_dec(v_impl_5268_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5395_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5388_; lean_object* v___x_5390_; 
v___x_5388_ = lean_unsigned_to_nat(3u);
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 4, v_l_5353_);
lean_ctor_set(v___x_5386_, 2, v_v_5260_);
lean_ctor_set(v___x_5386_, 1, v_k_5259_);
lean_ctor_set(v___x_5386_, 0, v___x_5269_);
v___x_5390_ = v___x_5386_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5394_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5394_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5394_, 3, v_l_5353_);
lean_ctor_set(v_reuseFailAlloc_5394_, 4, v_l_5353_);
v___x_5390_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
lean_object* v___x_5392_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_r_5382_);
lean_ctor_set(v___x_5264_, 3, v___x_5390_);
lean_ctor_set(v___x_5264_, 2, v_v_5384_);
lean_ctor_set(v___x_5264_, 1, v_k_5383_);
lean_ctor_set(v___x_5264_, 0, v___x_5388_);
v___x_5392_ = v___x_5264_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5388_);
lean_ctor_set(v_reuseFailAlloc_5393_, 1, v_k_5383_);
lean_ctor_set(v_reuseFailAlloc_5393_, 2, v_v_5384_);
lean_ctor_set(v_reuseFailAlloc_5393_, 3, v___x_5390_);
lean_ctor_set(v_reuseFailAlloc_5393_, 4, v_r_5382_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
v___x_5399_ = lean_unsigned_to_nat(2u);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_impl_5268_);
lean_ctor_set(v___x_5264_, 3, v_r_5382_);
lean_ctor_set(v___x_5264_, 0, v___x_5399_);
v___x_5401_ = v___x_5264_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5402_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5402_, 3, v_r_5382_);
lean_ctor_set(v_reuseFailAlloc_5402_, 4, v_impl_5268_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
}
else
{
lean_object* v___x_5404_; 
lean_dec(v_v_5260_);
lean_dec(v_k_5259_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 2, v_v_5256_);
lean_ctor_set(v___x_5264_, 1, v_k_5255_);
v___x_5404_ = v___x_5264_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_size_5258_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v_k_5255_);
lean_ctor_set(v_reuseFailAlloc_5405_, 2, v_v_5256_);
lean_ctor_set(v_reuseFailAlloc_5405_, 3, v_l_5261_);
lean_ctor_set(v_reuseFailAlloc_5405_, 4, v_r_5262_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
else
{
lean_object* v_impl_5406_; lean_object* v___x_5407_; 
lean_dec(v_size_5258_);
v_impl_5406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5255_, v_v_5256_, v_l_5261_);
v___x_5407_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5262_) == 0)
{
lean_object* v_size_5408_; lean_object* v_size_5409_; lean_object* v_k_5410_; lean_object* v_v_5411_; lean_object* v_l_5412_; lean_object* v_r_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; 
v_size_5408_ = lean_ctor_get(v_r_5262_, 0);
v_size_5409_ = lean_ctor_get(v_impl_5406_, 0);
lean_inc(v_size_5409_);
v_k_5410_ = lean_ctor_get(v_impl_5406_, 1);
lean_inc(v_k_5410_);
v_v_5411_ = lean_ctor_get(v_impl_5406_, 2);
lean_inc(v_v_5411_);
v_l_5412_ = lean_ctor_get(v_impl_5406_, 3);
lean_inc(v_l_5412_);
v_r_5413_ = lean_ctor_get(v_impl_5406_, 4);
lean_inc(v_r_5413_);
v___x_5414_ = lean_unsigned_to_nat(3u);
v___x_5415_ = lean_nat_mul(v___x_5414_, v_size_5408_);
v___x_5416_ = lean_nat_dec_lt(v___x_5415_, v_size_5409_);
lean_dec(v___x_5415_);
if (v___x_5416_ == 0)
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5420_; 
lean_dec(v_r_5413_);
lean_dec(v_l_5412_);
lean_dec(v_v_5411_);
lean_dec(v_k_5410_);
v___x_5417_ = lean_nat_add(v___x_5407_, v_size_5409_);
lean_dec(v_size_5409_);
v___x_5418_ = lean_nat_add(v___x_5417_, v_size_5408_);
lean_dec(v___x_5417_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 3, v_impl_5406_);
lean_ctor_set(v___x_5264_, 0, v___x_5418_);
v___x_5420_ = v___x_5264_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5421_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5421_, 3, v_impl_5406_);
lean_ctor_set(v_reuseFailAlloc_5421_, 4, v_r_5262_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
else
{
lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5487_; 
v_isSharedCheck_5487_ = !lean_is_exclusive(v_impl_5406_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; lean_object* v_unused_5489_; lean_object* v_unused_5490_; lean_object* v_unused_5491_; lean_object* v_unused_5492_; 
v_unused_5488_ = lean_ctor_get(v_impl_5406_, 4);
lean_dec(v_unused_5488_);
v_unused_5489_ = lean_ctor_get(v_impl_5406_, 3);
lean_dec(v_unused_5489_);
v_unused_5490_ = lean_ctor_get(v_impl_5406_, 2);
lean_dec(v_unused_5490_);
v_unused_5491_ = lean_ctor_get(v_impl_5406_, 1);
lean_dec(v_unused_5491_);
v_unused_5492_ = lean_ctor_get(v_impl_5406_, 0);
lean_dec(v_unused_5492_);
v___x_5423_ = v_impl_5406_;
v_isShared_5424_ = v_isSharedCheck_5487_;
goto v_resetjp_5422_;
}
else
{
lean_dec(v_impl_5406_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5487_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v_size_5425_; lean_object* v_size_5426_; lean_object* v_k_5427_; lean_object* v_v_5428_; lean_object* v_l_5429_; lean_object* v_r_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; 
v_size_5425_ = lean_ctor_get(v_l_5412_, 0);
v_size_5426_ = lean_ctor_get(v_r_5413_, 0);
v_k_5427_ = lean_ctor_get(v_r_5413_, 1);
v_v_5428_ = lean_ctor_get(v_r_5413_, 2);
v_l_5429_ = lean_ctor_get(v_r_5413_, 3);
v_r_5430_ = lean_ctor_get(v_r_5413_, 4);
v___x_5431_ = lean_unsigned_to_nat(2u);
v___x_5432_ = lean_nat_mul(v___x_5431_, v_size_5425_);
v___x_5433_ = lean_nat_dec_lt(v_size_5426_, v___x_5432_);
lean_dec(v___x_5432_);
if (v___x_5433_ == 0)
{
lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5462_; 
lean_inc(v_r_5430_);
lean_inc(v_l_5429_);
lean_inc(v_v_5428_);
lean_inc(v_k_5427_);
v_isSharedCheck_5462_ = !lean_is_exclusive(v_r_5413_);
if (v_isSharedCheck_5462_ == 0)
{
lean_object* v_unused_5463_; lean_object* v_unused_5464_; lean_object* v_unused_5465_; lean_object* v_unused_5466_; lean_object* v_unused_5467_; 
v_unused_5463_ = lean_ctor_get(v_r_5413_, 4);
lean_dec(v_unused_5463_);
v_unused_5464_ = lean_ctor_get(v_r_5413_, 3);
lean_dec(v_unused_5464_);
v_unused_5465_ = lean_ctor_get(v_r_5413_, 2);
lean_dec(v_unused_5465_);
v_unused_5466_ = lean_ctor_get(v_r_5413_, 1);
lean_dec(v_unused_5466_);
v_unused_5467_ = lean_ctor_get(v_r_5413_, 0);
lean_dec(v_unused_5467_);
v___x_5435_ = v_r_5413_;
v_isShared_5436_ = v_isSharedCheck_5462_;
goto v_resetjp_5434_;
}
else
{
lean_dec(v_r_5413_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5462_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___y_5440_; lean_object* v___y_5441_; lean_object* v___y_5442_; lean_object* v___x_5450_; lean_object* v___y_5452_; 
v___x_5437_ = lean_nat_add(v___x_5407_, v_size_5409_);
lean_dec(v_size_5409_);
v___x_5438_ = lean_nat_add(v___x_5437_, v_size_5408_);
lean_dec(v___x_5437_);
v___x_5450_ = lean_nat_add(v___x_5407_, v_size_5425_);
if (lean_obj_tag(v_l_5429_) == 0)
{
lean_object* v_size_5460_; 
v_size_5460_ = lean_ctor_get(v_l_5429_, 0);
lean_inc(v_size_5460_);
v___y_5452_ = v_size_5460_;
goto v___jp_5451_;
}
else
{
lean_object* v___x_5461_; 
v___x_5461_ = lean_unsigned_to_nat(0u);
v___y_5452_ = v___x_5461_;
goto v___jp_5451_;
}
v___jp_5439_:
{
lean_object* v___x_5443_; lean_object* v___x_5445_; 
v___x_5443_ = lean_nat_add(v___y_5441_, v___y_5442_);
lean_dec(v___y_5442_);
lean_dec(v___y_5441_);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 4, v_r_5262_);
lean_ctor_set(v___x_5435_, 3, v_r_5430_);
lean_ctor_set(v___x_5435_, 2, v_v_5260_);
lean_ctor_set(v___x_5435_, 1, v_k_5259_);
lean_ctor_set(v___x_5435_, 0, v___x_5443_);
v___x_5445_ = v___x_5435_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5449_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5449_, 3, v_r_5430_);
lean_ctor_set(v_reuseFailAlloc_5449_, 4, v_r_5262_);
v___x_5445_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5447_; 
if (v_isShared_5424_ == 0)
{
lean_ctor_set(v___x_5423_, 4, v___x_5445_);
lean_ctor_set(v___x_5423_, 3, v___y_5440_);
lean_ctor_set(v___x_5423_, 2, v_v_5428_);
lean_ctor_set(v___x_5423_, 1, v_k_5427_);
lean_ctor_set(v___x_5423_, 0, v___x_5438_);
v___x_5447_ = v___x_5423_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v_k_5427_);
lean_ctor_set(v_reuseFailAlloc_5448_, 2, v_v_5428_);
lean_ctor_set(v_reuseFailAlloc_5448_, 3, v___y_5440_);
lean_ctor_set(v_reuseFailAlloc_5448_, 4, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
v___jp_5451_:
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
v___x_5453_ = lean_nat_add(v___x_5450_, v___y_5452_);
lean_dec(v___y_5452_);
lean_dec(v___x_5450_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_l_5429_);
lean_ctor_set(v___x_5264_, 3, v_l_5412_);
lean_ctor_set(v___x_5264_, 2, v_v_5411_);
lean_ctor_set(v___x_5264_, 1, v_k_5410_);
lean_ctor_set(v___x_5264_, 0, v___x_5453_);
v___x_5455_ = v___x_5264_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v_k_5410_);
lean_ctor_set(v_reuseFailAlloc_5459_, 2, v_v_5411_);
lean_ctor_set(v_reuseFailAlloc_5459_, 3, v_l_5412_);
lean_ctor_set(v_reuseFailAlloc_5459_, 4, v_l_5429_);
v___x_5455_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5456_; 
v___x_5456_ = lean_nat_add(v___x_5407_, v_size_5408_);
if (lean_obj_tag(v_r_5430_) == 0)
{
lean_object* v_size_5457_; 
v_size_5457_ = lean_ctor_get(v_r_5430_, 0);
lean_inc(v_size_5457_);
v___y_5440_ = v___x_5455_;
v___y_5441_ = v___x_5456_;
v___y_5442_ = v_size_5457_;
goto v___jp_5439_;
}
else
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_unsigned_to_nat(0u);
v___y_5440_ = v___x_5455_;
v___y_5441_ = v___x_5456_;
v___y_5442_ = v___x_5458_;
goto v___jp_5439_;
}
}
}
}
}
else
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5473_; 
lean_del_object(v___x_5264_);
v___x_5468_ = lean_nat_add(v___x_5407_, v_size_5409_);
lean_dec(v_size_5409_);
v___x_5469_ = lean_nat_add(v___x_5468_, v_size_5408_);
lean_dec(v___x_5468_);
v___x_5470_ = lean_nat_add(v___x_5407_, v_size_5408_);
v___x_5471_ = lean_nat_add(v___x_5470_, v_size_5426_);
lean_dec(v___x_5470_);
lean_inc_ref(v_r_5262_);
if (v_isShared_5424_ == 0)
{
lean_ctor_set(v___x_5423_, 4, v_r_5262_);
lean_ctor_set(v___x_5423_, 3, v_r_5413_);
lean_ctor_set(v___x_5423_, 2, v_v_5260_);
lean_ctor_set(v___x_5423_, 1, v_k_5259_);
lean_ctor_set(v___x_5423_, 0, v___x_5471_);
v___x_5473_ = v___x_5423_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5486_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5486_, 3, v_r_5413_);
lean_ctor_set(v_reuseFailAlloc_5486_, 4, v_r_5262_);
v___x_5473_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
v_isSharedCheck_5480_ = !lean_is_exclusive(v_r_5262_);
if (v_isSharedCheck_5480_ == 0)
{
lean_object* v_unused_5481_; lean_object* v_unused_5482_; lean_object* v_unused_5483_; lean_object* v_unused_5484_; lean_object* v_unused_5485_; 
v_unused_5481_ = lean_ctor_get(v_r_5262_, 4);
lean_dec(v_unused_5481_);
v_unused_5482_ = lean_ctor_get(v_r_5262_, 3);
lean_dec(v_unused_5482_);
v_unused_5483_ = lean_ctor_get(v_r_5262_, 2);
lean_dec(v_unused_5483_);
v_unused_5484_ = lean_ctor_get(v_r_5262_, 1);
lean_dec(v_unused_5484_);
v_unused_5485_ = lean_ctor_get(v_r_5262_, 0);
lean_dec(v_unused_5485_);
v___x_5475_ = v_r_5262_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_dec(v_r_5262_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 4, v___x_5473_);
lean_ctor_set(v___x_5475_, 3, v_l_5412_);
lean_ctor_set(v___x_5475_, 2, v_v_5411_);
lean_ctor_set(v___x_5475_, 1, v_k_5410_);
lean_ctor_set(v___x_5475_, 0, v___x_5469_);
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5469_);
lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_k_5410_);
lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_v_5411_);
lean_ctor_set(v_reuseFailAlloc_5479_, 3, v_l_5412_);
lean_ctor_set(v_reuseFailAlloc_5479_, 4, v___x_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5493_; 
v_l_5493_ = lean_ctor_get(v_impl_5406_, 3);
lean_inc(v_l_5493_);
if (lean_obj_tag(v_l_5493_) == 0)
{
lean_object* v_r_5494_; lean_object* v_k_5495_; lean_object* v_v_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5507_; 
v_r_5494_ = lean_ctor_get(v_impl_5406_, 4);
v_k_5495_ = lean_ctor_get(v_impl_5406_, 1);
v_v_5496_ = lean_ctor_get(v_impl_5406_, 2);
v_isSharedCheck_5507_ = !lean_is_exclusive(v_impl_5406_);
if (v_isSharedCheck_5507_ == 0)
{
lean_object* v_unused_5508_; lean_object* v_unused_5509_; 
v_unused_5508_ = lean_ctor_get(v_impl_5406_, 3);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_impl_5406_, 0);
lean_dec(v_unused_5509_);
v___x_5498_ = v_impl_5406_;
v_isShared_5499_ = v_isSharedCheck_5507_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_r_5494_);
lean_inc(v_v_5496_);
lean_inc(v_k_5495_);
lean_dec(v_impl_5406_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5507_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5500_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5494_);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 3, v_r_5494_);
lean_ctor_set(v___x_5498_, 2, v_v_5260_);
lean_ctor_set(v___x_5498_, 1, v_k_5259_);
lean_ctor_set(v___x_5498_, 0, v___x_5407_);
v___x_5502_ = v___x_5498_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5506_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5506_, 3, v_r_5494_);
lean_ctor_set(v_reuseFailAlloc_5506_, 4, v_r_5494_);
v___x_5502_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v___x_5502_);
lean_ctor_set(v___x_5264_, 3, v_l_5493_);
lean_ctor_set(v___x_5264_, 2, v_v_5496_);
lean_ctor_set(v___x_5264_, 1, v_k_5495_);
lean_ctor_set(v___x_5264_, 0, v___x_5500_);
v___x_5504_ = v___x_5264_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5500_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_k_5495_);
lean_ctor_set(v_reuseFailAlloc_5505_, 2, v_v_5496_);
lean_ctor_set(v_reuseFailAlloc_5505_, 3, v_l_5493_);
lean_ctor_set(v_reuseFailAlloc_5505_, 4, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
else
{
lean_object* v_r_5510_; 
v_r_5510_ = lean_ctor_get(v_impl_5406_, 4);
lean_inc(v_r_5510_);
if (lean_obj_tag(v_r_5510_) == 0)
{
lean_object* v_k_5511_; lean_object* v_v_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5535_; 
v_k_5511_ = lean_ctor_get(v_impl_5406_, 1);
v_v_5512_ = lean_ctor_get(v_impl_5406_, 2);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_impl_5406_);
if (v_isSharedCheck_5535_ == 0)
{
lean_object* v_unused_5536_; lean_object* v_unused_5537_; lean_object* v_unused_5538_; 
v_unused_5536_ = lean_ctor_get(v_impl_5406_, 4);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_impl_5406_, 3);
lean_dec(v_unused_5537_);
v_unused_5538_ = lean_ctor_get(v_impl_5406_, 0);
lean_dec(v_unused_5538_);
v___x_5514_ = v_impl_5406_;
v_isShared_5515_ = v_isSharedCheck_5535_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_v_5512_);
lean_inc(v_k_5511_);
lean_dec(v_impl_5406_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5535_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_k_5516_; lean_object* v_v_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5531_; 
v_k_5516_ = lean_ctor_get(v_r_5510_, 1);
v_v_5517_ = lean_ctor_get(v_r_5510_, 2);
v_isSharedCheck_5531_ = !lean_is_exclusive(v_r_5510_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; lean_object* v_unused_5533_; lean_object* v_unused_5534_; 
v_unused_5532_ = lean_ctor_get(v_r_5510_, 4);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_r_5510_, 3);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_r_5510_, 0);
lean_dec(v_unused_5534_);
v___x_5519_ = v_r_5510_;
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_v_5517_);
lean_inc(v_k_5516_);
lean_dec(v_r_5510_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
v___x_5521_ = lean_unsigned_to_nat(3u);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 4, v_l_5493_);
lean_ctor_set(v___x_5519_, 3, v_l_5493_);
lean_ctor_set(v___x_5519_, 2, v_v_5512_);
lean_ctor_set(v___x_5519_, 1, v_k_5511_);
lean_ctor_set(v___x_5519_, 0, v___x_5407_);
v___x_5523_ = v___x_5519_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_k_5511_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_v_5512_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_l_5493_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_l_5493_);
v___x_5523_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5525_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 4, v_l_5493_);
lean_ctor_set(v___x_5514_, 2, v_v_5260_);
lean_ctor_set(v___x_5514_, 1, v_k_5259_);
lean_ctor_set(v___x_5514_, 0, v___x_5407_);
v___x_5525_ = v___x_5514_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v_l_5493_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_l_5493_);
v___x_5525_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v___x_5525_);
lean_ctor_set(v___x_5264_, 3, v___x_5523_);
lean_ctor_set(v___x_5264_, 2, v_v_5517_);
lean_ctor_set(v___x_5264_, 1, v_k_5516_);
lean_ctor_set(v___x_5264_, 0, v___x_5521_);
v___x_5527_ = v___x_5264_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v_k_5516_);
lean_ctor_set(v_reuseFailAlloc_5528_, 2, v_v_5517_);
lean_ctor_set(v_reuseFailAlloc_5528_, 3, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5528_, 4, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
}
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5539_ = lean_unsigned_to_nat(2u);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_r_5510_);
lean_ctor_set(v___x_5264_, 3, v_impl_5406_);
lean_ctor_set(v___x_5264_, 0, v___x_5539_);
v___x_5541_ = v___x_5264_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_v_5260_);
lean_ctor_set(v_reuseFailAlloc_5542_, 3, v_impl_5406_);
lean_ctor_set(v_reuseFailAlloc_5542_, 4, v_r_5510_);
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
}
else
{
lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5544_ = lean_unsigned_to_nat(1u);
v___x_5545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
lean_ctor_set(v___x_5545_, 1, v_k_5255_);
lean_ctor_set(v___x_5545_, 2, v_v_5256_);
lean_ctor_set(v___x_5545_, 3, v_t_5257_);
lean_ctor_set(v___x_5545_, 4, v_t_5257_);
return v___x_5545_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5546_, lean_object* v_t_5547_){
_start:
{
if (lean_obj_tag(v_t_5547_) == 0)
{
lean_object* v_k_5548_; lean_object* v_l_5549_; lean_object* v_r_5550_; uint8_t v___x_5551_; 
v_k_5548_ = lean_ctor_get(v_t_5547_, 1);
v_l_5549_ = lean_ctor_get(v_t_5547_, 3);
v_r_5550_ = lean_ctor_get(v_t_5547_, 4);
v___x_5551_ = lean_nat_dec_lt(v_k_5548_, v_k_5546_);
if (v___x_5551_ == 0)
{
uint8_t v___x_5552_; 
v___x_5552_ = lean_nat_dec_eq(v_k_5548_, v_k_5546_);
if (v___x_5552_ == 0)
{
v_t_5547_ = v_r_5550_;
goto _start;
}
else
{
return v___x_5552_;
}
}
else
{
v_t_5547_ = v_l_5549_;
goto _start;
}
}
else
{
uint8_t v___x_5555_; 
v___x_5555_ = 0;
return v___x_5555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5556_, lean_object* v_t_5557_){
_start:
{
uint8_t v_res_5558_; lean_object* v_r_5559_; 
v_res_5558_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5556_, v_t_5557_);
lean_dec(v_t_5557_);
lean_dec(v_k_5556_);
v_r_5559_ = lean_box(v_res_5558_);
return v_r_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5560_, lean_object* v_e_5561_){
_start:
{
lean_object* v_defaultInstances_5562_; lean_object* v_priorities_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5590_; 
v_defaultInstances_5562_ = lean_ctor_get(v_d_5560_, 0);
v_priorities_5563_ = lean_ctor_get(v_d_5560_, 1);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_d_5560_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5565_ = v_d_5560_;
v_isShared_5566_ = v_isSharedCheck_5590_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_priorities_5563_);
lean_inc(v_defaultInstances_5562_);
lean_dec(v_d_5560_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5590_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v_className_5567_; lean_object* v_instanceName_5568_; lean_object* v_priority_5569_; lean_object* v___y_5571_; uint8_t v___x_5587_; 
v_className_5567_ = lean_ctor_get(v_e_5561_, 0);
lean_inc(v_className_5567_);
v_instanceName_5568_ = lean_ctor_get(v_e_5561_, 1);
lean_inc(v_instanceName_5568_);
v_priority_5569_ = lean_ctor_get(v_e_5561_, 2);
lean_inc(v_priority_5569_);
lean_dec_ref(v_e_5561_);
v___x_5587_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5569_, v_priorities_5563_);
if (v___x_5587_ == 0)
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_box(0);
lean_inc(v_priority_5569_);
v___x_5589_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5569_, v___x_5588_, v_priorities_5563_);
v___y_5571_ = v___x_5589_;
goto v___jp_5570_;
}
else
{
v___y_5571_ = v_priorities_5563_;
goto v___jp_5570_;
}
v___jp_5570_:
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5562_, v_className_5567_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5578_; 
v___x_5573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5573_, 0, v_instanceName_5568_);
lean_ctor_set(v___x_5573_, 1, v_priority_5569_);
v___x_5574_ = lean_box(0);
v___x_5575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5573_);
lean_ctor_set(v___x_5575_, 1, v___x_5574_);
v___x_5576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5567_, v___x_5575_, v_defaultInstances_5562_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 1, v___y_5571_);
lean_ctor_set(v___x_5565_, 0, v___x_5576_);
v___x_5578_ = v___x_5565_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v___y_5571_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
else
{
lean_object* v_val_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5585_; 
v_val_5580_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_val_5580_);
lean_dec_ref_known(v___x_5572_, 1);
v___x_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5581_, 0, v_instanceName_5568_);
lean_ctor_set(v___x_5581_, 1, v_priority_5569_);
v___x_5582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
lean_ctor_set(v___x_5582_, 1, v_val_5580_);
v___x_5583_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5567_, v___x_5582_, v_defaultInstances_5562_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 1, v___y_5571_);
lean_ctor_set(v___x_5565_, 0, v___x_5583_);
v___x_5585_ = v___x_5565_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___y_5571_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5591_, lean_object* v_k_5592_, lean_object* v_t_5593_){
_start:
{
uint8_t v___x_5594_; 
v___x_5594_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5592_, v_t_5593_);
return v___x_5594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5595_, lean_object* v_k_5596_, lean_object* v_t_5597_){
_start:
{
uint8_t v_res_5598_; lean_object* v_r_5599_; 
v_res_5598_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5595_, v_k_5596_, v_t_5597_);
lean_dec(v_t_5597_);
lean_dec(v_k_5596_);
v_r_5599_ = lean_box(v_res_5598_);
return v_r_5599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5600_, lean_object* v_k_5601_, lean_object* v_v_5602_, lean_object* v_t_5603_, lean_object* v_hl_5604_){
_start:
{
lean_object* v___x_5605_; 
v___x_5605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5601_, v_v_5602_, v_t_5603_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5606_, lean_object* v_as_5607_, size_t v_i_5608_, size_t v_stop_5609_, lean_object* v_b_5610_){
_start:
{
lean_object* v___y_5612_; uint8_t v___x_5616_; 
v___x_5616_ = lean_usize_dec_eq(v_i_5608_, v_stop_5609_);
if (v___x_5616_ == 0)
{
lean_object* v___x_5617_; lean_object* v_instanceName_5618_; uint8_t v___x_5619_; lean_object* v___x_5620_; uint8_t v___x_5621_; 
v___x_5617_ = lean_array_uget_borrowed(v_as_5607_, v_i_5608_);
v_instanceName_5618_ = lean_ctor_get(v___x_5617_, 1);
v___x_5619_ = 1;
lean_inc_ref(v_env_5606_);
v___x_5620_ = l_Lean_Environment_setExporting(v_env_5606_, v___x_5619_);
lean_inc(v_instanceName_5618_);
v___x_5621_ = l_Lean_Environment_contains(v___x_5620_, v_instanceName_5618_, v___x_5616_);
if (v___x_5621_ == 0)
{
v___y_5612_ = v_b_5610_;
goto v___jp_5611_;
}
else
{
lean_object* v___x_5622_; 
lean_inc(v___x_5617_);
v___x_5622_ = lean_array_push(v_b_5610_, v___x_5617_);
v___y_5612_ = v___x_5622_;
goto v___jp_5611_;
}
}
else
{
lean_dec_ref(v_env_5606_);
return v_b_5610_;
}
v___jp_5611_:
{
size_t v___x_5613_; size_t v___x_5614_; 
v___x_5613_ = ((size_t)1ULL);
v___x_5614_ = lean_usize_add(v_i_5608_, v___x_5613_);
v_i_5608_ = v___x_5614_;
v_b_5610_ = v___y_5612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5623_, lean_object* v_as_5624_, lean_object* v_i_5625_, lean_object* v_stop_5626_, lean_object* v_b_5627_){
_start:
{
size_t v_i_boxed_5628_; size_t v_stop_boxed_5629_; lean_object* v_res_5630_; 
v_i_boxed_5628_ = lean_unbox_usize(v_i_5625_);
lean_dec(v_i_5625_);
v_stop_boxed_5629_ = lean_unbox_usize(v_stop_5626_);
lean_dec(v_stop_5626_);
v_res_5630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5623_, v_as_5624_, v_i_boxed_5628_, v_stop_boxed_5629_, v_b_5627_);
lean_dec_ref(v_as_5624_);
return v_res_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5633_, lean_object* v_x_5634_, lean_object* v_entries_5635_){
_start:
{
lean_object* v_all_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; uint8_t v___x_5640_; 
v_all_5636_ = lean_array_mk(v_entries_5635_);
v___x_5637_ = lean_unsigned_to_nat(0u);
v___x_5638_ = lean_array_get_size(v_all_5636_);
v___x_5639_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5640_ = lean_nat_dec_lt(v___x_5637_, v___x_5638_);
if (v___x_5640_ == 0)
{
lean_object* v___x_5641_; 
lean_dec_ref(v_env_5633_);
v___x_5641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5639_);
lean_ctor_set(v___x_5641_, 1, v___x_5639_);
lean_ctor_set(v___x_5641_, 2, v_all_5636_);
return v___x_5641_;
}
else
{
uint8_t v___x_5642_; 
v___x_5642_ = lean_nat_dec_le(v___x_5638_, v___x_5638_);
if (v___x_5642_ == 0)
{
if (v___x_5640_ == 0)
{
lean_object* v___x_5643_; 
lean_dec_ref(v_env_5633_);
v___x_5643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5639_);
lean_ctor_set(v___x_5643_, 1, v___x_5639_);
lean_ctor_set(v___x_5643_, 2, v_all_5636_);
return v___x_5643_;
}
else
{
size_t v___x_5644_; size_t v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
v___x_5644_ = ((size_t)0ULL);
v___x_5645_ = lean_usize_of_nat(v___x_5638_);
v___x_5646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5633_, v_all_5636_, v___x_5644_, v___x_5645_, v___x_5639_);
lean_inc_ref(v___x_5646_);
v___x_5647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
lean_ctor_set(v___x_5647_, 2, v_all_5636_);
return v___x_5647_;
}
}
else
{
size_t v___x_5648_; size_t v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5648_ = ((size_t)0ULL);
v___x_5649_ = lean_usize_of_nat(v___x_5638_);
v___x_5650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5633_, v_all_5636_, v___x_5648_, v___x_5649_, v___x_5639_);
lean_inc_ref(v___x_5650_);
v___x_5651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set(v___x_5651_, 1, v___x_5650_);
lean_ctor_set(v___x_5651_, 2, v_all_5636_);
return v___x_5651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5652_, lean_object* v_x_5653_, lean_object* v_entries_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5652_, v_x_5653_, v_entries_5654_);
lean_dec_ref(v_x_5653_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5656_){
_start:
{
lean_object* v___x_5657_; 
v___x_5657_ = lean_array_mk(v_es_5656_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5658_, size_t v_i_5659_, size_t v_stop_5660_, lean_object* v_b_5661_){
_start:
{
uint8_t v___x_5662_; 
v___x_5662_ = lean_usize_dec_eq(v_i_5659_, v_stop_5660_);
if (v___x_5662_ == 0)
{
lean_object* v___x_5663_; lean_object* v___x_5664_; size_t v___x_5665_; size_t v___x_5666_; 
v___x_5663_ = lean_array_uget_borrowed(v_as_5658_, v_i_5659_);
lean_inc(v___x_5663_);
v___x_5664_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5661_, v___x_5663_);
v___x_5665_ = ((size_t)1ULL);
v___x_5666_ = lean_usize_add(v_i_5659_, v___x_5665_);
v_i_5659_ = v___x_5666_;
v_b_5661_ = v___x_5664_;
goto _start;
}
else
{
return v_b_5661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5668_, lean_object* v_i_5669_, lean_object* v_stop_5670_, lean_object* v_b_5671_){
_start:
{
size_t v_i_boxed_5672_; size_t v_stop_boxed_5673_; lean_object* v_res_5674_; 
v_i_boxed_5672_ = lean_unbox_usize(v_i_5669_);
lean_dec(v_i_5669_);
v_stop_boxed_5673_ = lean_unbox_usize(v_stop_5670_);
lean_dec(v_stop_5670_);
v_res_5674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5668_, v_i_boxed_5672_, v_stop_boxed_5673_, v_b_5671_);
lean_dec_ref(v_as_5668_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5675_, size_t v_i_5676_, size_t v_stop_5677_, lean_object* v_b_5678_){
_start:
{
lean_object* v___y_5680_; uint8_t v___x_5684_; 
v___x_5684_ = lean_usize_dec_eq(v_i_5676_, v_stop_5677_);
if (v___x_5684_ == 0)
{
lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; uint8_t v___x_5688_; 
v___x_5685_ = lean_array_uget_borrowed(v_as_5675_, v_i_5676_);
v___x_5686_ = lean_unsigned_to_nat(0u);
v___x_5687_ = lean_array_get_size(v___x_5685_);
v___x_5688_ = lean_nat_dec_lt(v___x_5686_, v___x_5687_);
if (v___x_5688_ == 0)
{
v___y_5680_ = v_b_5678_;
goto v___jp_5679_;
}
else
{
uint8_t v___x_5689_; 
v___x_5689_ = lean_nat_dec_le(v___x_5687_, v___x_5687_);
if (v___x_5689_ == 0)
{
if (v___x_5688_ == 0)
{
v___y_5680_ = v_b_5678_;
goto v___jp_5679_;
}
else
{
size_t v___x_5690_; size_t v___x_5691_; lean_object* v___x_5692_; 
v___x_5690_ = ((size_t)0ULL);
v___x_5691_ = lean_usize_of_nat(v___x_5687_);
v___x_5692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5685_, v___x_5690_, v___x_5691_, v_b_5678_);
v___y_5680_ = v___x_5692_;
goto v___jp_5679_;
}
}
else
{
size_t v___x_5693_; size_t v___x_5694_; lean_object* v___x_5695_; 
v___x_5693_ = ((size_t)0ULL);
v___x_5694_ = lean_usize_of_nat(v___x_5687_);
v___x_5695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5685_, v___x_5693_, v___x_5694_, v_b_5678_);
v___y_5680_ = v___x_5695_;
goto v___jp_5679_;
}
}
}
else
{
return v_b_5678_;
}
v___jp_5679_:
{
size_t v___x_5681_; size_t v___x_5682_; 
v___x_5681_ = ((size_t)1ULL);
v___x_5682_ = lean_usize_add(v_i_5676_, v___x_5681_);
v_i_5676_ = v___x_5682_;
v_b_5678_ = v___y_5680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5696_, lean_object* v_i_5697_, lean_object* v_stop_5698_, lean_object* v_b_5699_){
_start:
{
size_t v_i_boxed_5700_; size_t v_stop_boxed_5701_; lean_object* v_res_5702_; 
v_i_boxed_5700_ = lean_unbox_usize(v_i_5697_);
lean_dec(v_i_5697_);
v_stop_boxed_5701_ = lean_unbox_usize(v_stop_5698_);
lean_dec(v_stop_5698_);
v_res_5702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5696_, v_i_boxed_5700_, v_stop_boxed_5701_, v_b_5699_);
lean_dec_ref(v_as_5696_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5703_, lean_object* v_as_5704_){
_start:
{
lean_object* v___x_5705_; lean_object* v___x_5706_; uint8_t v___x_5707_; 
v___x_5705_ = lean_unsigned_to_nat(0u);
v___x_5706_ = lean_array_get_size(v_as_5704_);
v___x_5707_ = lean_nat_dec_lt(v___x_5705_, v___x_5706_);
if (v___x_5707_ == 0)
{
return v_initState_5703_;
}
else
{
uint8_t v___x_5708_; 
v___x_5708_ = lean_nat_dec_le(v___x_5706_, v___x_5706_);
if (v___x_5708_ == 0)
{
if (v___x_5707_ == 0)
{
return v_initState_5703_;
}
else
{
size_t v___x_5709_; size_t v___x_5710_; lean_object* v___x_5711_; 
v___x_5709_ = ((size_t)0ULL);
v___x_5710_ = lean_usize_of_nat(v___x_5706_);
v___x_5711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5704_, v___x_5709_, v___x_5710_, v_initState_5703_);
return v___x_5711_;
}
}
else
{
size_t v___x_5712_; size_t v___x_5713_; lean_object* v___x_5714_; 
v___x_5712_ = ((size_t)0ULL);
v___x_5713_ = lean_usize_of_nat(v___x_5706_);
v___x_5714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5704_, v___x_5712_, v___x_5713_, v_initState_5703_);
return v___x_5714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5715_, lean_object* v_as_5716_){
_start:
{
lean_object* v_res_5717_; 
v_res_5717_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5715_, v_as_5716_);
lean_dec_ref(v_as_5716_);
return v_res_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5718_){
_start:
{
lean_object* v___x_5719_; lean_object* v___x_5720_; 
v___x_5719_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5720_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5719_, v_es_5718_);
return v___x_5720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5721_){
_start:
{
lean_object* v_res_5722_; 
v_res_5722_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5721_);
lean_dec_ref(v_es_5721_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; 
v___x_5743_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5744_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5743_);
return v___x_5744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_){
_start:
{
lean_object* v___x_5751_; lean_object* v_nextMacroScope_5752_; lean_object* v_ngen_5753_; lean_object* v_auxDeclNGen_5754_; lean_object* v_traceState_5755_; lean_object* v_messages_5756_; lean_object* v_infoState_5757_; lean_object* v_snapshotTasks_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5784_; 
v___x_5751_ = lean_st_ref_take(v___y_5749_);
v_nextMacroScope_5752_ = lean_ctor_get(v___x_5751_, 1);
v_ngen_5753_ = lean_ctor_get(v___x_5751_, 2);
v_auxDeclNGen_5754_ = lean_ctor_get(v___x_5751_, 3);
v_traceState_5755_ = lean_ctor_get(v___x_5751_, 4);
v_messages_5756_ = lean_ctor_get(v___x_5751_, 6);
v_infoState_5757_ = lean_ctor_get(v___x_5751_, 7);
v_snapshotTasks_5758_ = lean_ctor_get(v___x_5751_, 8);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5751_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; lean_object* v_unused_5786_; 
v_unused_5785_ = lean_ctor_get(v___x_5751_, 5);
lean_dec(v_unused_5785_);
v_unused_5786_ = lean_ctor_get(v___x_5751_, 0);
lean_dec(v_unused_5786_);
v___x_5760_ = v___x_5751_;
v_isShared_5761_ = v_isSharedCheck_5784_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_snapshotTasks_5758_);
lean_inc(v_infoState_5757_);
lean_inc(v_messages_5756_);
lean_inc(v_traceState_5755_);
lean_inc(v_auxDeclNGen_5754_);
lean_inc(v_ngen_5753_);
lean_inc(v_nextMacroScope_5752_);
lean_dec(v___x_5751_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5784_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5762_; lean_object* v___x_5764_; 
v___x_5762_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 5, v___x_5762_);
lean_ctor_set(v___x_5760_, 0, v_env_5747_);
v___x_5764_ = v___x_5760_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_env_5747_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_nextMacroScope_5752_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_ngen_5753_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_auxDeclNGen_5754_);
lean_ctor_set(v_reuseFailAlloc_5783_, 4, v_traceState_5755_);
lean_ctor_set(v_reuseFailAlloc_5783_, 5, v___x_5762_);
lean_ctor_set(v_reuseFailAlloc_5783_, 6, v_messages_5756_);
lean_ctor_set(v_reuseFailAlloc_5783_, 7, v_infoState_5757_);
lean_ctor_set(v_reuseFailAlloc_5783_, 8, v_snapshotTasks_5758_);
v___x_5764_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v_mctx_5767_; lean_object* v_zetaDeltaFVarIds_5768_; lean_object* v_postponed_5769_; lean_object* v_diag_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5781_; 
v___x_5765_ = lean_st_ref_set(v___y_5749_, v___x_5764_);
v___x_5766_ = lean_st_ref_take(v___y_5748_);
v_mctx_5767_ = lean_ctor_get(v___x_5766_, 0);
v_zetaDeltaFVarIds_5768_ = lean_ctor_get(v___x_5766_, 2);
v_postponed_5769_ = lean_ctor_get(v___x_5766_, 3);
v_diag_5770_ = lean_ctor_get(v___x_5766_, 4);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5766_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v___x_5766_, 1);
lean_dec(v_unused_5782_);
v___x_5772_ = v___x_5766_;
v_isShared_5773_ = v_isSharedCheck_5781_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_diag_5770_);
lean_inc(v_postponed_5769_);
lean_inc(v_zetaDeltaFVarIds_5768_);
lean_inc(v_mctx_5767_);
lean_dec(v___x_5766_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5781_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5774_; lean_object* v___x_5776_; 
v___x_5774_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5773_ == 0)
{
lean_ctor_set(v___x_5772_, 1, v___x_5774_);
v___x_5776_ = v___x_5772_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_mctx_5767_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5780_, 2, v_zetaDeltaFVarIds_5768_);
lean_ctor_set(v_reuseFailAlloc_5780_, 3, v_postponed_5769_);
lean_ctor_set(v_reuseFailAlloc_5780_, 4, v_diag_5770_);
v___x_5776_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; 
v___x_5777_ = lean_st_ref_set(v___y_5748_, v___x_5776_);
v___x_5778_ = lean_box(0);
v___x_5779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5778_);
return v___x_5779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5787_, v___y_5788_, v___y_5789_);
lean_dec(v___y_5789_);
lean_dec(v___y_5788_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5792_, v___y_5794_, v___y_5796_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
return v_res_5805_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5808_ = l_Lean_stringToMessageData(v___x_5807_);
return v___x_5808_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5811_ = l_Lean_stringToMessageData(v___x_5810_);
return v___x_5811_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5814_ = l_Lean_stringToMessageData(v___x_5813_);
return v___x_5814_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5817_ = l_Lean_stringToMessageData(v___x_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5819_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5820_ = l_Lean_stringToMessageData(v___x_5819_);
return v___x_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5821_, lean_object* v_prio_5822_, lean_object* v_x_5823_, lean_object* v_type_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_){
_start:
{
lean_object* v___x_5830_; 
v___x_5830_ = l_Lean_Expr_getAppFn(v_type_5824_);
if (lean_obj_tag(v___x_5830_) == 4)
{
lean_object* v_declName_5831_; lean_object* v___y_5833_; lean_object* v___y_5834_; lean_object* v___y_5835_; lean_object* v___y_5836_; lean_object* v___x_5846_; lean_object* v_env_5847_; uint8_t v___x_5848_; 
v_declName_5831_ = lean_ctor_get(v___x_5830_, 0);
lean_inc_n(v_declName_5831_, 2);
lean_dec_ref_known(v___x_5830_, 2);
v___x_5846_ = lean_st_ref_get(v___y_5828_);
v_env_5847_ = lean_ctor_get(v___x_5846_, 0);
lean_inc_ref(v_env_5847_);
lean_dec(v___x_5846_);
v___x_5848_ = lean_is_class(v_env_5847_, v_declName_5831_);
if (v___x_5848_ == 0)
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
lean_dec(v_prio_5822_);
v___x_5849_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5850_ = l_Lean_MessageData_ofConstName(v_declName_5821_, v___x_5848_);
v___x_5851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5849_);
lean_ctor_set(v___x_5851_, 1, v___x_5850_);
v___x_5852_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5851_);
lean_ctor_set(v___x_5853_, 1, v___x_5852_);
lean_inc(v_declName_5831_);
v___x_5854_ = l_Lean_MessageData_ofName(v_declName_5831_);
v___x_5855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5855_, 0, v___x_5853_);
lean_ctor_set(v___x_5855_, 1, v___x_5854_);
v___x_5856_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5857_, 0, v___x_5855_);
lean_ctor_set(v___x_5857_, 1, v___x_5856_);
v___x_5858_ = l_Lean_MessageData_ofConstName(v_declName_5831_, v___x_5848_);
v___x_5859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5857_);
lean_ctor_set(v___x_5859_, 1, v___x_5858_);
v___x_5860_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5859_);
lean_ctor_set(v___x_5861_, 1, v___x_5860_);
v___x_5862_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5861_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_);
return v___x_5862_;
}
else
{
v___y_5833_ = v___y_5825_;
v___y_5834_ = v___y_5826_;
v___y_5835_ = v___y_5827_;
v___y_5836_ = v___y_5828_;
goto v___jp_5832_;
}
v___jp_5832_:
{
lean_object* v___x_5837_; lean_object* v_env_5838_; lean_object* v___x_5839_; lean_object* v_toEnvExtension_5840_; lean_object* v_asyncMode_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5837_ = lean_st_ref_get(v___y_5836_);
v_env_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc_ref(v_env_5838_);
lean_dec(v___x_5837_);
v___x_5839_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5840_ = lean_ctor_get(v___x_5839_, 0);
v_asyncMode_5841_ = lean_ctor_get(v_toEnvExtension_5840_, 2);
v___x_5842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5842_, 0, v_declName_5831_);
lean_ctor_set(v___x_5842_, 1, v_declName_5821_);
lean_ctor_set(v___x_5842_, 2, v_prio_5822_);
v___x_5843_ = lean_box(0);
v___x_5844_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5839_, v_env_5838_, v___x_5842_, v_asyncMode_5841_, v___x_5843_);
v___x_5845_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5844_, v___y_5834_, v___y_5836_);
return v___x_5845_;
}
}
else
{
lean_object* v___x_5863_; uint8_t v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
lean_dec_ref(v___x_5830_);
lean_dec(v_prio_5822_);
v___x_5863_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5864_ = 0;
v___x_5865_ = l_Lean_MessageData_ofConstName(v_declName_5821_, v___x_5864_);
v___x_5866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5863_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
v___x_5867_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5866_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5868_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_);
return v___x_5869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5870_, lean_object* v_prio_5871_, lean_object* v_x_5872_, lean_object* v_type_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_){
_start:
{
lean_object* v_res_5879_; 
v_res_5879_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5870_, v_prio_5871_, v_x_5872_, v_type_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
lean_dec(v___y_5877_);
lean_dec_ref(v___y_5876_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec_ref(v_type_5873_);
lean_dec_ref(v_x_5872_);
return v_res_5879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5880_, lean_object* v_prio_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_){
_start:
{
lean_object* v___x_5887_; lean_object* v_env_5888_; uint8_t v___x_5889_; lean_object* v___x_5890_; 
v___x_5887_ = lean_st_ref_get(v_a_5885_);
v_env_5888_ = lean_ctor_get(v___x_5887_, 0);
lean_inc_ref(v_env_5888_);
lean_dec(v___x_5887_);
v___x_5889_ = 0;
lean_inc(v_declName_5880_);
v___x_5890_ = l_Lean_Environment_find_x3f(v_env_5888_, v_declName_5880_, v___x_5889_);
if (lean_obj_tag(v___x_5890_) == 0)
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; 
lean_dec(v_prio_5881_);
v___x_5891_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5892_ = l_Lean_MessageData_ofConstName(v_declName_5880_, v___x_5889_);
v___x_5893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5891_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
v___x_5894_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5893_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5895_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_);
return v___x_5896_;
}
else
{
lean_object* v_val_5897_; lean_object* v___f_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v_val_5897_ = lean_ctor_get(v___x_5890_, 0);
lean_inc(v_val_5897_);
lean_dec_ref_known(v___x_5890_, 1);
v___f_5898_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5898_, 0, v_declName_5880_);
lean_closure_set(v___f_5898_, 1, v_prio_5881_);
v___x_5899_ = l_Lean_ConstantInfo_type(v_val_5897_);
lean_dec(v_val_5897_);
v___x_5900_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5899_, v___f_5898_, v___x_5889_, v___x_5889_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_);
return v___x_5900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5901_, lean_object* v_prio_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_, lean_object* v_a_5907_){
_start:
{
lean_object* v_res_5908_; 
v_res_5908_ = l_Lean_Meta_addDefaultInstance(v_declName_5901_, v_prio_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_);
lean_dec(v_a_5906_);
lean_dec_ref(v_a_5905_);
lean_dec(v_a_5904_);
lean_dec_ref(v_a_5903_);
return v_res_5908_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5910_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5911_ = l_Lean_stringToMessageData(v___x_5910_);
return v___x_5911_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5913_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5914_ = l_Lean_stringToMessageData(v___x_5913_);
return v___x_5914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5918_, uint8_t v_kind_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___y_5929_; 
v___x_5923_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5924_ = l_Lean_MessageData_ofName(v_name_5918_);
v___x_5925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5923_);
lean_ctor_set(v___x_5925_, 1, v___x_5924_);
v___x_5926_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5925_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
switch(v_kind_5919_)
{
case 0:
{
lean_object* v___x_5936_; 
v___x_5936_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5929_ = v___x_5936_;
goto v___jp_5928_;
}
case 1:
{
lean_object* v___x_5937_; 
v___x_5937_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5929_ = v___x_5937_;
goto v___jp_5928_;
}
default: 
{
lean_object* v___x_5938_; 
v___x_5938_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5929_ = v___x_5938_;
goto v___jp_5928_;
}
}
v___jp_5928_:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
lean_inc_ref(v___y_5929_);
v___x_5930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5930_, 0, v___y_5929_);
v___x_5931_ = l_Lean_MessageData_ofFormat(v___x_5930_);
v___x_5932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5927_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5934_, v___y_5920_, v___y_5921_);
return v___x_5935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5939_, lean_object* v_kind_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_){
_start:
{
uint8_t v_kind_boxed_5944_; lean_object* v_res_5945_; 
v_kind_boxed_5944_ = lean_unbox(v_kind_5940_);
v_res_5945_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5939_, v_kind_boxed_5944_, v___y_5941_, v___y_5942_);
lean_dec(v___y_5942_);
lean_dec_ref(v___y_5941_);
return v_res_5945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5946_, lean_object* v___x_5947_, lean_object* v___x_5948_, lean_object* v_declName_5949_, lean_object* v_stx_5950_, uint8_t v_kind_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5955_ = lean_unsigned_to_nat(1u);
v___x_5956_ = l_Lean_Syntax_getArg(v_stx_5950_, v___x_5955_);
v___x_5957_ = l_Lean_getAttrParamOptPrio(v___x_5956_, v___y_5952_, v___y_5953_);
if (lean_obj_tag(v___x_5957_) == 0)
{
lean_object* v_a_5958_; lean_object* v___y_5960_; lean_object* v___y_5961_; uint8_t v___x_5992_; uint8_t v___x_5993_; 
v_a_5958_ = lean_ctor_get(v___x_5957_, 0);
lean_inc(v_a_5958_);
lean_dec_ref_known(v___x_5957_, 1);
v___x_5992_ = 0;
v___x_5993_ = l_Lean_instBEqAttributeKind_beq(v_kind_5951_, v___x_5992_);
if (v___x_5993_ == 0)
{
lean_object* v___x_5994_; 
lean_dec(v_a_5958_);
lean_dec(v_declName_5949_);
lean_dec(v___x_5947_);
lean_dec(v___x_5946_);
v___x_5994_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5948_, v_kind_5951_, v___y_5952_, v___y_5953_);
return v___x_5994_;
}
else
{
lean_dec(v___x_5948_);
v___y_5960_ = v___y_5952_;
v___y_5961_ = v___y_5953_;
goto v___jp_5959_;
}
v___jp_5959_:
{
uint8_t v___x_5962_; uint8_t v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; size_t v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5962_ = 0;
v___x_5963_ = 1;
v___x_5964_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5965_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5966_ = lean_unsigned_to_nat(32u);
v___x_5967_ = lean_mk_empty_array_with_capacity(v___x_5966_);
v___x_5968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_5969_ = ((size_t)5ULL);
lean_inc_n(v___x_5946_, 6);
v___x_5970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5970_, 0, v___x_5968_);
lean_ctor_set(v___x_5970_, 1, v___x_5967_);
lean_ctor_set(v___x_5970_, 2, v___x_5946_);
lean_ctor_set(v___x_5970_, 3, v___x_5946_);
lean_ctor_set_usize(v___x_5970_, 4, v___x_5969_);
v___x_5971_ = lean_box(1);
lean_inc_ref(v___x_5970_);
v___x_5972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5965_);
lean_ctor_set(v___x_5972_, 1, v___x_5970_);
lean_ctor_set(v___x_5972_, 2, v___x_5971_);
v___x_5973_ = lean_mk_empty_array_with_capacity(v___x_5946_);
v___x_5974_ = lean_box(0);
lean_inc(v___x_5947_);
v___x_5975_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5975_, 0, v___x_5964_);
lean_ctor_set(v___x_5975_, 1, v___x_5947_);
lean_ctor_set(v___x_5975_, 2, v___x_5972_);
lean_ctor_set(v___x_5975_, 3, v___x_5973_);
lean_ctor_set(v___x_5975_, 4, v___x_5974_);
lean_ctor_set(v___x_5975_, 5, v___x_5946_);
lean_ctor_set(v___x_5975_, 6, v___x_5974_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*7, v___x_5962_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*7 + 1, v___x_5962_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*7 + 2, v___x_5962_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*7 + 3, v___x_5963_);
v___x_5976_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5946_);
lean_ctor_set(v___x_5976_, 1, v___x_5946_);
lean_ctor_set(v___x_5976_, 2, v___x_5946_);
lean_ctor_set(v___x_5976_, 3, v___x_5946_);
lean_ctor_set(v___x_5976_, 4, v___x_5965_);
lean_ctor_set(v___x_5976_, 5, v___x_5965_);
lean_ctor_set(v___x_5976_, 6, v___x_5965_);
lean_ctor_set(v___x_5976_, 7, v___x_5965_);
lean_ctor_set(v___x_5976_, 8, v___x_5965_);
lean_ctor_set(v___x_5976_, 9, v___x_5965_);
v___x_5977_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5978_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5976_);
lean_ctor_set(v___x_5979_, 1, v___x_5977_);
lean_ctor_set(v___x_5979_, 2, v___x_5947_);
lean_ctor_set(v___x_5979_, 3, v___x_5970_);
lean_ctor_set(v___x_5979_, 4, v___x_5978_);
v___x_5980_ = lean_st_mk_ref(v___x_5979_);
v___x_5981_ = l_Lean_Meta_addDefaultInstance(v_declName_5949_, v_a_5958_, v___x_5975_, v___x_5980_, v___y_5960_, v___y_5961_);
lean_dec_ref_known(v___x_5975_, 7);
if (lean_obj_tag(v___x_5981_) == 0)
{
lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_5990_; 
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5981_);
if (v_isSharedCheck_5990_ == 0)
{
lean_object* v_unused_5991_; 
v_unused_5991_ = lean_ctor_get(v___x_5981_, 0);
lean_dec(v_unused_5991_);
v___x_5983_ = v___x_5981_;
v_isShared_5984_ = v_isSharedCheck_5990_;
goto v_resetjp_5982_;
}
else
{
lean_dec(v___x_5981_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5990_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5988_; 
v___x_5985_ = lean_st_ref_get(v___x_5980_);
lean_dec(v___x_5980_);
lean_dec(v___x_5985_);
v___x_5986_ = lean_box(0);
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 0, v___x_5986_);
v___x_5988_ = v___x_5983_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
else
{
lean_dec(v___x_5980_);
return v___x_5981_;
}
}
}
else
{
lean_object* v_a_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6002_; 
lean_dec(v_declName_5949_);
lean_dec(v___x_5948_);
lean_dec(v___x_5947_);
lean_dec(v___x_5946_);
v_a_5995_ = lean_ctor_get(v___x_5957_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5957_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5997_ = v___x_5957_;
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_a_5995_);
lean_dec(v___x_5957_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
lean_object* v___x_6000_; 
if (v_isShared_5998_ == 0)
{
v___x_6000_ = v___x_5997_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_a_5995_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6003_, lean_object* v___x_6004_, lean_object* v___x_6005_, lean_object* v_declName_6006_, lean_object* v_stx_6007_, lean_object* v_kind_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_){
_start:
{
uint8_t v_kind_boxed_6012_; lean_object* v_res_6013_; 
v_kind_boxed_6012_ = lean_unbox(v_kind_6008_);
v_res_6013_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6003_, v___x_6004_, v___x_6005_, v_declName_6006_, v_stx_6007_, v_kind_boxed_6012_, v___y_6009_, v___y_6010_);
lean_dec(v___y_6010_);
lean_dec_ref(v___y_6009_);
lean_dec(v_stx_6007_);
return v_res_6013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6015_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6016_ = l_Lean_stringToMessageData(v___x_6015_);
return v___x_6016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6018_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6019_ = l_Lean_stringToMessageData(v___x_6018_);
return v___x_6019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6020_, lean_object* v_decl_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6025_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6026_ = l_Lean_MessageData_ofName(v___x_6020_);
v___x_6027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6025_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6027_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6029_, v___y_6022_, v___y_6023_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6031_, lean_object* v_decl_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_){
_start:
{
lean_object* v_res_6036_; 
v_res_6036_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6031_, v_decl_6032_, v___y_6033_, v___y_6034_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec(v_decl_6032_);
return v_res_6036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6069_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6070_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6071_ = l_Lean_registerBuiltinAttribute(v___x_6070_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_object* v___x_6072_; uint8_t v___x_6073_; lean_object* v___x_6074_; 
lean_dec_ref_known(v___x_6071_, 1);
v___x_6072_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6073_ = 0;
v___x_6074_ = l_Lean_registerTraceClass(v___x_6072_, v___x_6073_, v___x_6069_);
return v___x_6074_;
}
else
{
return v___x_6071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6077_, lean_object* v_name_6078_, uint8_t v_kind_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v___x_6083_; 
v___x_6083_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6078_, v_kind_6079_, v___y_6080_, v___y_6081_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6084_, lean_object* v_name_6085_, lean_object* v_kind_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_){
_start:
{
uint8_t v_kind_boxed_6090_; lean_object* v_res_6091_; 
v_kind_boxed_6090_ = lean_unbox(v_kind_6086_);
v_res_6091_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6084_, v_name_6085_, v_kind_boxed_6090_, v___y_6087_, v___y_6088_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6092_, lean_object* v_toPure_6093_, lean_object* v_____do__lift_6094_){
_start:
{
lean_object* v___x_6095_; lean_object* v_toEnvExtension_6096_; lean_object* v_asyncMode_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v_priorities_6100_; lean_object* v___x_6101_; 
v___x_6095_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6096_ = lean_ctor_get(v___x_6095_, 0);
v_asyncMode_6097_ = lean_ctor_get(v_toEnvExtension_6096_, 2);
v___x_6098_ = lean_box(0);
v___x_6099_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6092_, v___x_6095_, v_____do__lift_6094_, v_asyncMode_6097_, v___x_6098_);
v_priorities_6100_ = lean_ctor_get(v___x_6099_, 1);
lean_inc(v_priorities_6100_);
lean_dec(v___x_6099_);
v___x_6101_ = lean_apply_2(v_toPure_6093_, lean_box(0), v_priorities_6100_);
return v___x_6101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6102_, lean_object* v_inst_6103_){
_start:
{
lean_object* v_toApplicative_6104_; lean_object* v_toBind_6105_; lean_object* v_getEnv_6106_; lean_object* v_toPure_6107_; lean_object* v___x_6108_; lean_object* v___f_6109_; lean_object* v___x_6110_; 
v_toApplicative_6104_ = lean_ctor_get(v_inst_6102_, 0);
lean_inc_ref(v_toApplicative_6104_);
v_toBind_6105_ = lean_ctor_get(v_inst_6102_, 1);
lean_inc(v_toBind_6105_);
lean_dec_ref(v_inst_6102_);
v_getEnv_6106_ = lean_ctor_get(v_inst_6103_, 0);
lean_inc(v_getEnv_6106_);
lean_dec_ref(v_inst_6103_);
v_toPure_6107_ = lean_ctor_get(v_toApplicative_6104_, 1);
lean_inc(v_toPure_6107_);
lean_dec_ref(v_toApplicative_6104_);
v___x_6108_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6109_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6109_, 0, v___x_6108_);
lean_closure_set(v___f_6109_, 1, v_toPure_6107_);
v___x_6110_ = lean_apply_4(v_toBind_6105_, lean_box(0), lean_box(0), v_getEnv_6106_, v___f_6109_);
return v___x_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6111_, lean_object* v_inst_6112_, lean_object* v_inst_6113_){
_start:
{
lean_object* v___x_6114_; 
v___x_6114_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6112_, v_inst_6113_);
return v___x_6114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6115_, uint8_t v_isExporting_6116_, lean_object* v_x_6117_){
_start:
{
lean_object* v_fst_6118_; uint8_t v___x_6119_; 
v_fst_6118_ = lean_ctor_get(v_x_6117_, 0);
lean_inc(v_fst_6118_);
lean_dec_ref(v_x_6117_);
v___x_6119_ = l_Lean_Environment_contains(v_env_6115_, v_fst_6118_, v_isExporting_6116_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6120_, lean_object* v_isExporting_6121_, lean_object* v_x_6122_){
_start:
{
uint8_t v_isExporting_boxed_6123_; uint8_t v_res_6124_; lean_object* v_r_6125_; 
v_isExporting_boxed_6123_ = lean_unbox(v_isExporting_6121_);
v_res_6124_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6120_, v_isExporting_boxed_6123_, v_x_6122_);
v_r_6125_ = lean_box(v_res_6124_);
return v_r_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6126_, lean_object* v_toApplicative_6127_, lean_object* v_className_6128_, lean_object* v_env_6129_){
_start:
{
lean_object* v___y_6131_; lean_object* v___x_6141_; lean_object* v_toEnvExtension_6142_; lean_object* v_asyncMode_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v_defaultInstances_6146_; lean_object* v___x_6147_; 
v___x_6141_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6142_ = lean_ctor_get(v___x_6141_, 0);
v_asyncMode_6143_ = lean_ctor_get(v_toEnvExtension_6142_, 2);
v___x_6144_ = lean_box(0);
lean_inc_ref(v_env_6129_);
v___x_6145_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6126_, v___x_6141_, v_env_6129_, v_asyncMode_6143_, v___x_6144_);
v_defaultInstances_6146_ = lean_ctor_get(v___x_6145_, 0);
lean_inc(v_defaultInstances_6146_);
lean_dec(v___x_6145_);
v___x_6147_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6146_, v_className_6128_);
lean_dec(v_defaultInstances_6146_);
if (lean_obj_tag(v___x_6147_) == 0)
{
lean_object* v___x_6148_; 
v___x_6148_ = lean_box(0);
v___y_6131_ = v___x_6148_;
goto v___jp_6130_;
}
else
{
lean_object* v_val_6149_; 
v_val_6149_ = lean_ctor_get(v___x_6147_, 0);
lean_inc(v_val_6149_);
lean_dec_ref_known(v___x_6147_, 1);
v___y_6131_ = v_val_6149_;
goto v___jp_6130_;
}
v___jp_6130_:
{
uint8_t v_isExporting_6132_; 
v_isExporting_6132_ = lean_ctor_get_uint8(v_env_6129_, sizeof(void*)*8);
if (v_isExporting_6132_ == 0)
{
lean_object* v_toPure_6133_; lean_object* v___x_6134_; 
lean_dec_ref(v_env_6129_);
v_toPure_6133_ = lean_ctor_get(v_toApplicative_6127_, 1);
lean_inc(v_toPure_6133_);
lean_dec_ref(v_toApplicative_6127_);
v___x_6134_ = lean_apply_2(v_toPure_6133_, lean_box(0), v___y_6131_);
return v___x_6134_;
}
else
{
lean_object* v_toPure_6135_; lean_object* v___x_6136_; lean_object* v___f_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; 
v_toPure_6135_ = lean_ctor_get(v_toApplicative_6127_, 1);
lean_inc(v_toPure_6135_);
lean_dec_ref(v_toApplicative_6127_);
v___x_6136_ = lean_box(v_isExporting_6132_);
v___f_6137_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6137_, 0, v_env_6129_);
lean_closure_set(v___f_6137_, 1, v___x_6136_);
v___x_6138_ = lean_box(0);
v___x_6139_ = l_List_filterTR_loop___redArg(v___f_6137_, v___y_6131_, v___x_6138_);
v___x_6140_ = lean_apply_2(v_toPure_6135_, lean_box(0), v___x_6139_);
return v___x_6140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6150_, lean_object* v_toApplicative_6151_, lean_object* v_className_6152_, lean_object* v_env_6153_){
_start:
{
lean_object* v_res_6154_; 
v_res_6154_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6150_, v_toApplicative_6151_, v_className_6152_, v_env_6153_);
lean_dec(v_className_6152_);
return v_res_6154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6155_, lean_object* v_inst_6156_, lean_object* v_className_6157_){
_start:
{
lean_object* v_toApplicative_6158_; lean_object* v_toBind_6159_; lean_object* v_getEnv_6160_; lean_object* v___x_6161_; lean_object* v___f_6162_; lean_object* v___x_6163_; 
v_toApplicative_6158_ = lean_ctor_get(v_inst_6155_, 0);
lean_inc_ref(v_toApplicative_6158_);
v_toBind_6159_ = lean_ctor_get(v_inst_6155_, 1);
lean_inc(v_toBind_6159_);
lean_dec_ref(v_inst_6155_);
v_getEnv_6160_ = lean_ctor_get(v_inst_6156_, 0);
lean_inc(v_getEnv_6160_);
lean_dec_ref(v_inst_6156_);
v___x_6161_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6162_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6162_, 0, v___x_6161_);
lean_closure_set(v___f_6162_, 1, v_toApplicative_6158_);
lean_closure_set(v___f_6162_, 2, v_className_6157_);
v___x_6163_ = lean_apply_4(v_toBind_6159_, lean_box(0), lean_box(0), v_getEnv_6160_, v___f_6162_);
return v___x_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6164_, lean_object* v_inst_6165_, lean_object* v_inst_6166_, lean_object* v_className_6167_){
_start:
{
lean_object* v___x_6168_; 
v___x_6168_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6165_, v_inst_6166_, v_className_6167_);
return v___x_6168_;
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
