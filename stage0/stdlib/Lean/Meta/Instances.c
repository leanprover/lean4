// Lean compiler output
// Module: Lean.Meta.Instances
// Imports: public import Init.Data.Range.Polymorphic.Stream public import Lean.Meta.DiscrTree.Main public import Lean.Meta.CollectMVars import Init.While import Lean.OriginalConstKind import Lean.ProjFns
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_range(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Instance "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " has arguments "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = " that are impossible to infer. Those arguments are not instance-implicit and do not appear in another instance-implicit argument or the return type."};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instance `"};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` target `"};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a type class."};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` must be marked with `@[expose]`"};
static const lean_object* l_Lean_Meta_addInstance___closed__0 = (const lean_object*)&l_Lean_Meta_addInstance___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__1;
static const lean_string_object l_Lean_Meta_addInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` must be marked with `@[reducible]` or `@[implicit_reducible]`"};
static const lean_object* l_Lean_Meta_addInstance___closed__2 = (const lean_object*)&l_Lean_Meta_addInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_426_);
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
lean_dec_ref(v___x_703_);
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
lean_dec_ref(v_entry_749_);
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
lean_dec_ref(v___x_771_);
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
lean_dec_ref(v___x_801_);
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
lean_dec_ref(v___x_1192_);
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
lean_dec_ref(v___x_1222_);
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
lean_dec_ref(v___x_1361_);
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
lean_dec_ref(v___x_1446_);
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
lean_dec_ref(v___x_1466_);
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
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Lean_instInhabitedExpr;
v___x_1737_ = lean_array_get_borrowed(v___x_1736_, v_argVars_1699_, v_val_1735_);
lean_dec(v_val_1735_);
lean_inc(v___x_1737_);
lean_inc(v_a_1712_);
v___x_1738_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1712_, v___x_1737_, v___y_1705_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref(v___x_1738_);
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
lean_dec_ref(v___x_1719_);
v___x_1721_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1698_, v_argVars_1699_, v_a_1720_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1721_) == 0)
{
size_t v___x_1722_; size_t v___x_1723_; 
lean_dec_ref(v___x_1721_);
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
lean_dec_ref(v___x_1747_);
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
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v_val_1907_) == 1)
{
uint8_t v_v_1908_; 
v_v_1908_ = lean_ctor_get_uint8(v_val_1907_, 0);
lean_dec_ref(v_val_1907_);
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
lean_dec_ref(v___x_1984_);
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
lean_dec_ref(v___x_2099_);
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
lean_dec_ref(v___x_2214_);
v___x_2216_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2215_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_dummy_2218_; lean_object* v_nargs_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
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
lean_dec_ref(v_fst_2233_);
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
uint8_t v___x_26277__boxed_2277_; lean_object* v_res_2278_; 
v___x_26277__boxed_2277_ = lean_unbox(v___x_2269_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2267_, v___x_2268_, v___x_26277__boxed_2277_, v_x_2270_, v_argTy_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
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
lean_dec_ref(v___x_2300_);
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
lean_dec_ref(v___x_2339_);
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
lean_dec_ref(v___y_2317_);
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
lean_dec_ref(v___x_2396_);
v___x_2398_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2397_, v___y_2387_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v_bs_x27_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2398_);
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
lean_dec_ref(v___x_2493_);
v___x_2495_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2479_, v_argVars_2480_, v_a_2494_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v___x_2496_; 
lean_dec_ref(v___x_2495_);
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
lean_dec_ref(v_a_2580_);
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
lean_dec_ref(v_a_2580_);
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
lean_dec_ref(v___x_2611_);
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
lean_dec_ref(v_fst_2613_);
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
lean_dec_ref(v_val_2659_);
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
lean_dec_ref(v___x_2623_);
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
lean_dec_ref(v___x_2639_);
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
lean_object* v_ref_2700_; lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2747_; 
v_ref_2700_ = lean_ctor_get(v___y_2697_, 5);
v___x_2701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2747_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2747_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v_traceState_2707_; lean_object* v_env_2708_; lean_object* v_nextMacroScope_2709_; lean_object* v_ngen_2710_; lean_object* v_auxDeclNGen_2711_; lean_object* v_cache_2712_; lean_object* v_messages_2713_; lean_object* v_infoState_2714_; lean_object* v_snapshotTasks_2715_; lean_object* v_newDecls_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2746_; 
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
v_newDecls_2716_ = lean_ctor_get(v___x_2706_, 9);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2718_ = v___x_2706_;
v_isShared_2719_ = v_isSharedCheck_2746_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_newDecls_2716_);
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
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2746_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint64_t v_tid_2720_; lean_object* v_traces_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2745_; 
v_tid_2720_ = lean_ctor_get_uint64(v_traceState_2707_, sizeof(void*)*1);
v_traces_2721_ = lean_ctor_get(v_traceState_2707_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_traceState_2707_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2723_ = v_traceState_2707_;
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_traces_2721_);
lean_dec(v_traceState_2707_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; double v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2727_ = 0;
v___x_2728_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2729_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2729_, 0, v_cls_2693_);
lean_ctor_set(v___x_2729_, 1, v___x_2725_);
lean_ctor_set(v___x_2729_, 2, v___x_2728_);
lean_ctor_set_float(v___x_2729_, sizeof(void*)*3, v___x_2726_);
lean_ctor_set_float(v___x_2729_, sizeof(void*)*3 + 8, v___x_2726_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*3 + 16, v___x_2727_);
v___x_2730_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2731_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v_a_2702_);
lean_ctor_set(v___x_2731_, 2, v___x_2730_);
lean_inc(v_ref_2700_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_ref_2700_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = l_Lean_PersistentArray_push___redArg(v_traces_2721_, v___x_2732_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2733_);
v___x_2735_ = v___x_2723_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2733_);
lean_ctor_set_uint64(v_reuseFailAlloc_2744_, sizeof(void*)*1, v_tid_2720_);
v___x_2735_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 4, v___x_2735_);
v___x_2737_ = v___x_2718_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_env_2708_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_nextMacroScope_2709_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_ngen_2710_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_auxDeclNGen_2711_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2743_, 5, v_cache_2712_);
lean_ctor_set(v_reuseFailAlloc_2743_, 6, v_messages_2713_);
lean_ctor_set(v_reuseFailAlloc_2743_, 7, v_infoState_2714_);
lean_ctor_set(v_reuseFailAlloc_2743_, 8, v_snapshotTasks_2715_);
lean_ctor_set(v_reuseFailAlloc_2743_, 9, v_newDecls_2716_);
v___x_2737_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2738_ = lean_st_ref_set(v___y_2698_, v___x_2737_);
v___x_2739_ = lean_box(0);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2739_);
v___x_2741_ = v___x_2704_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2748_, lean_object* v_msg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2748_, v_msg_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2765_ = l_Lean_Name_append(v___x_2764_, v___x_2763_);
return v___x_2765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2774_ = l_Lean_stringToMessageData(v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2777_ = l_Lean_stringToMessageData(v___x_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2778_, lean_object* v_fst_2779_, lean_object* v_fst_2780_, lean_object* v_inst_2781_, lean_object* v_a_2782_, lean_object* v_projInfo_x3f_2783_, lean_object* v_argVars_2784_, lean_object* v_x_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2778_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v_dummy_2793_; lean_object* v_nargs_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; size_t v_sz_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v_dummy_2793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2794_ = l_Lean_Expr_getAppNumArgs(v_a_2778_);
lean_inc(v_nargs_2794_);
v___x_2795_ = lean_mk_array(v_nargs_2794_, v_dummy_2793_);
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_nat_sub(v_nargs_2794_, v___x_2796_);
lean_dec(v_nargs_2794_);
lean_inc_ref(v_a_2778_);
v___x_2798_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2778_, v___x_2795_, v___x_2797_);
v___x_2799_ = lean_array_get_size(v___x_2798_);
v___x_2800_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
v_sz_2802_ = lean_array_size(v___x_2798_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2792_, v_fst_2779_, v_argVars_2784_, v___x_2798_, v_sz_2802_, v___x_2803_, v___x_2801_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec_ref(v___x_2798_);
lean_dec(v_a_2792_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec_ref(v___x_2804_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2806_ = lean_array_get_size(v_fst_2779_);
v___x_2807_ = l_List_range(v___x_2806_);
v___x_2808_ = lean_box(0);
v___x_2809_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2780_, v___x_2807_, v___x_2808_);
v___x_2810_ = lean_array_mk(v___x_2809_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2805_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
lean_inc_ref(v_inst_2781_);
lean_inc_ref(v_argVars_2784_);
v___x_2812_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2779_, v_argVars_2784_, v_inst_2781_, v_a_2782_, v_projInfo_x3f_2783_, v___x_2811_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2905_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2905_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2905_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_fst_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2903_; 
v_fst_2817_ = lean_ctor_get(v_a_2813_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_a_2813_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v_a_2813_, 1);
lean_dec(v_unused_2904_);
v___x_2819_ = v_a_2813_;
v_isShared_2820_ = v_isSharedCheck_2903_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_fst_2817_);
lean_dec(v_a_2813_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2903_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_options_2825_; lean_object* v_inheritedTraceOptions_2826_; lean_object* v___y_2827_; lean_object* v_options_2883_; lean_object* v_inheritedTraceOptions_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v_options_2883_ = lean_ctor_get(v___y_2788_, 2);
v_inheritedTraceOptions_2884_ = lean_ctor_get(v___y_2788_, 13);
v___x_2885_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2886_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2883_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v_a_2778_);
v___y_2822_ = v___y_2786_;
v___y_2823_ = v___y_2787_;
v___y_2824_ = v___y_2788_;
v_options_2825_ = v_options_2883_;
v_inheritedTraceOptions_2826_ = v_inheritedTraceOptions_2884_;
v___y_2827_ = v___y_2789_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2887_; lean_object* v_a_2888_; uint8_t v___x_2889_; 
v___x_2887_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2778_, v___y_2787_);
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = l_Lean_Expr_hasExprMVar(v_a_2888_);
if (v___x_2889_ == 0)
{
lean_dec(v_a_2888_);
v___y_2822_ = v___y_2786_;
v___y_2823_ = v___y_2787_;
v___y_2824_ = v___y_2788_;
v_options_2825_ = v_options_2883_;
v_inheritedTraceOptions_2826_ = v_inheritedTraceOptions_2884_;
v___y_2827_ = v___y_2789_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2819_);
lean_dec(v_fst_2817_);
lean_del_object(v___x_2815_);
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_inst_2781_);
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2891_ = l_Lean_Expr_setPPExplicit(v_a_2888_, v___x_2889_);
v___x_2892_ = l_Lean_indentExpr(v___x_2891_);
v___x_2893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2890_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2893_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
v___jp_2821_:
{
uint8_t v_hasTrace_2828_; 
v_hasTrace_2828_ = lean_ctor_get_uint8(v_options_2825_, sizeof(void*)*1);
if (v_hasTrace_2828_ == 0)
{
lean_object* v___x_2830_; 
lean_del_object(v___x_2819_);
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_inst_2781_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v_fst_2817_);
v___x_2830_ = v___x_2815_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_fst_2817_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2833_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2826_, v_options_2825_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2836_; 
lean_del_object(v___x_2819_);
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_inst_2781_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v_fst_2817_);
v___x_2836_ = v___x_2815_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_fst_2817_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
size_t v_sz_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2815_);
v_sz_2838_ = lean_array_size(v_fst_2817_);
lean_inc(v_fst_2817_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2784_, v_sz_2838_, v___x_2803_, v_fst_2817_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2827_);
lean_dec_ref(v_argVars_2784_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2842_ = l_Lean_MessageData_ofExpr(v_inst_2781_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 7);
lean_ctor_set(v___x_2819_, 1, v___x_2842_);
lean_ctor_set(v___x_2819_, 0, v___x_2841_);
v___x_2844_ = v___x_2819_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2845_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
lean_inc(v_fst_2817_);
v___x_2847_ = lean_array_to_list(v_fst_2817_);
v___x_2848_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2847_, v___x_2808_);
v___x_2849_ = l_Lean_MessageData_ofList(v___x_2848_);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2846_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_array_to_list(v_a_2840_);
v___x_2854_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2855_ = l_Lean_MessageData_joinSep(v___x_2853_, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2852_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2832_, v___x_2856_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2827_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2865_);
v___x_2859_ = v___x_2857_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v___x_2857_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_fst_2817_);
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_fst_2817_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_fst_2817_);
v_a_2866_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2857_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2857_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_del_object(v___x_2819_);
lean_dec(v_fst_2817_);
lean_dec_ref(v_inst_2781_);
v_a_2875_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2839_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2839_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
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
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_inst_2781_);
lean_dec_ref(v_a_2778_);
v_a_2906_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2812_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2812_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_a_2782_);
lean_dec_ref(v_inst_2781_);
lean_dec_ref(v_fst_2779_);
lean_dec_ref(v_a_2778_);
v_a_2914_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2804_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2804_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2784_);
lean_dec_ref(v_a_2782_);
lean_dec_ref(v_inst_2781_);
lean_dec_ref(v_fst_2779_);
lean_dec_ref(v_a_2778_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2922_, lean_object* v_fst_2923_, lean_object* v_fst_2924_, lean_object* v_inst_2925_, lean_object* v_a_2926_, lean_object* v_projInfo_x3f_2927_, lean_object* v_argVars_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2922_, v_fst_2923_, v_fst_2924_, v_inst_2925_, v_a_2926_, v_projInfo_x3f_2927_, v_argVars_2928_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v_x_2929_);
lean_dec(v_projInfo_x3f_2927_);
lean_dec_ref(v_fst_2924_);
return v_res_2935_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2936_; uint64_t v___x_2937_; 
v___x_2936_ = 2;
v___x_2937_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2938_, lean_object* v_projInfo_x3f_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2945_; uint8_t v_foApprox_2946_; uint8_t v_ctxApprox_2947_; uint8_t v_quasiPatternApprox_2948_; uint8_t v_constApprox_2949_; uint8_t v_isDefEqStuckEx_2950_; uint8_t v_unificationHints_2951_; uint8_t v_proofIrrelevance_2952_; uint8_t v_assignSyntheticOpaque_2953_; uint8_t v_offsetCnstrs_2954_; uint8_t v_etaStruct_2955_; uint8_t v_univApprox_2956_; uint8_t v_iota_2957_; uint8_t v_beta_2958_; uint8_t v_proj_2959_; uint8_t v_zeta_2960_; uint8_t v_zetaDelta_2961_; uint8_t v_zetaUnused_2962_; uint8_t v_zetaHave_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3028_; 
v___x_2945_ = l_Lean_Meta_Context_config(v_a_2940_);
v_foApprox_2946_ = lean_ctor_get_uint8(v___x_2945_, 0);
v_ctxApprox_2947_ = lean_ctor_get_uint8(v___x_2945_, 1);
v_quasiPatternApprox_2948_ = lean_ctor_get_uint8(v___x_2945_, 2);
v_constApprox_2949_ = lean_ctor_get_uint8(v___x_2945_, 3);
v_isDefEqStuckEx_2950_ = lean_ctor_get_uint8(v___x_2945_, 4);
v_unificationHints_2951_ = lean_ctor_get_uint8(v___x_2945_, 5);
v_proofIrrelevance_2952_ = lean_ctor_get_uint8(v___x_2945_, 6);
v_assignSyntheticOpaque_2953_ = lean_ctor_get_uint8(v___x_2945_, 7);
v_offsetCnstrs_2954_ = lean_ctor_get_uint8(v___x_2945_, 8);
v_etaStruct_2955_ = lean_ctor_get_uint8(v___x_2945_, 10);
v_univApprox_2956_ = lean_ctor_get_uint8(v___x_2945_, 11);
v_iota_2957_ = lean_ctor_get_uint8(v___x_2945_, 12);
v_beta_2958_ = lean_ctor_get_uint8(v___x_2945_, 13);
v_proj_2959_ = lean_ctor_get_uint8(v___x_2945_, 14);
v_zeta_2960_ = lean_ctor_get_uint8(v___x_2945_, 15);
v_zetaDelta_2961_ = lean_ctor_get_uint8(v___x_2945_, 16);
v_zetaUnused_2962_ = lean_ctor_get_uint8(v___x_2945_, 17);
v_zetaHave_2963_ = lean_ctor_get_uint8(v___x_2945_, 18);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2965_ = v___x_2945_;
v_isShared_2966_ = v_isSharedCheck_3028_;
goto v_resetjp_2964_;
}
else
{
lean_dec(v___x_2945_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3028_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
uint8_t v_trackZetaDelta_2967_; lean_object* v_zetaDeltaSet_2968_; lean_object* v_lctx_2969_; lean_object* v_localInstances_2970_; lean_object* v_defEqCtx_x3f_2971_; lean_object* v_synthPendingDepth_2972_; lean_object* v_canUnfold_x3f_2973_; uint8_t v_univApprox_2974_; uint8_t v_inTypeClassResolution_2975_; uint8_t v_cacheInferType_2976_; uint8_t v___x_2977_; lean_object* v_config_2979_; 
v_trackZetaDelta_2967_ = lean_ctor_get_uint8(v_a_2940_, sizeof(void*)*7);
v_zetaDeltaSet_2968_ = lean_ctor_get(v_a_2940_, 1);
v_lctx_2969_ = lean_ctor_get(v_a_2940_, 2);
v_localInstances_2970_ = lean_ctor_get(v_a_2940_, 3);
v_defEqCtx_x3f_2971_ = lean_ctor_get(v_a_2940_, 4);
v_synthPendingDepth_2972_ = lean_ctor_get(v_a_2940_, 5);
v_canUnfold_x3f_2973_ = lean_ctor_get(v_a_2940_, 6);
v_univApprox_2974_ = lean_ctor_get_uint8(v_a_2940_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2975_ = lean_ctor_get_uint8(v_a_2940_, sizeof(void*)*7 + 2);
v_cacheInferType_2976_ = lean_ctor_get_uint8(v_a_2940_, sizeof(void*)*7 + 3);
v___x_2977_ = 2;
if (v_isShared_2966_ == 0)
{
v_config_2979_ = v___x_2965_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 0, v_foApprox_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 1, v_ctxApprox_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 2, v_quasiPatternApprox_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 3, v_constApprox_2949_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 4, v_isDefEqStuckEx_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 5, v_unificationHints_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 6, v_proofIrrelevance_2952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 7, v_assignSyntheticOpaque_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 8, v_offsetCnstrs_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 10, v_etaStruct_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 11, v_univApprox_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 12, v_iota_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 13, v_beta_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 14, v_proj_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 15, v_zeta_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 16, v_zetaDelta_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 17, v_zetaUnused_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, 18, v_zetaHave_2963_);
v_config_2979_ = v_reuseFailAlloc_3027_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
uint64_t v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; uint64_t v___x_2984_; uint64_t v_key_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_ctor_set_uint8(v_config_2979_, 9, v___x_2977_);
v___x_2980_ = l_Lean_Meta_Context_configKey(v_a_2940_);
v___x_2981_ = 2ULL;
v___x_2982_ = lean_uint64_shift_right(v___x_2980_, v___x_2981_);
v___x_2983_ = lean_uint64_shift_left(v___x_2982_, v___x_2981_);
v___x_2984_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2985_ = lean_uint64_lor(v___x_2983_, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2986_, 0, v_config_2979_);
lean_ctor_set_uint64(v___x_2986_, sizeof(void*)*1, v_key_2985_);
lean_inc(v_canUnfold_x3f_2973_);
lean_inc(v_synthPendingDepth_2972_);
lean_inc(v_defEqCtx_x3f_2971_);
lean_inc_ref(v_localInstances_2970_);
lean_inc_ref(v_lctx_2969_);
lean_inc(v_zetaDeltaSet_2968_);
v___x_2987_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_zetaDeltaSet_2968_);
lean_ctor_set(v___x_2987_, 2, v_lctx_2969_);
lean_ctor_set(v___x_2987_, 3, v_localInstances_2970_);
lean_ctor_set(v___x_2987_, 4, v_defEqCtx_x3f_2971_);
lean_ctor_set(v___x_2987_, 5, v_synthPendingDepth_2972_);
lean_ctor_set(v___x_2987_, 6, v_canUnfold_x3f_2973_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7, v_trackZetaDelta_2967_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 1, v_univApprox_2974_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2975_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 3, v_cacheInferType_2976_);
lean_inc(v_a_2943_);
lean_inc_ref(v_a_2942_);
lean_inc(v_a_2941_);
lean_inc_ref(v___x_2987_);
lean_inc_ref(v_inst_2938_);
v___x_2988_ = lean_infer_type(v_inst_2938_, v___x_2987_, v_a_2941_, v_a_2942_, v_a_2943_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_n(v_a_2989_, 2);
lean_dec_ref(v___x_2988_);
v___x_2990_ = lean_box(0);
v___x_2991_ = 0;
v___x_2992_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2989_, v___x_2990_, v___x_2991_, v___x_2987_, v_a_2941_, v_a_2942_, v_a_2943_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_snd_2994_; lean_object* v_fst_2995_; lean_object* v_fst_2996_; lean_object* v_snd_2997_; lean_object* v___x_2998_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref(v___x_2992_);
v_snd_2994_ = lean_ctor_get(v_a_2993_, 1);
lean_inc(v_snd_2994_);
v_fst_2995_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_fst_2995_);
lean_dec(v_a_2993_);
v_fst_2996_ = lean_ctor_get(v_snd_2994_, 0);
lean_inc(v_fst_2996_);
v_snd_2997_ = lean_ctor_get(v_snd_2994_, 1);
lean_inc(v_snd_2997_);
lean_dec(v_snd_2994_);
lean_inc(v_a_2943_);
lean_inc_ref(v_a_2942_);
lean_inc(v_a_2941_);
lean_inc_ref(v___x_2987_);
v___x_2998_ = lean_whnf(v_snd_2997_, v___x_2987_, v_a_2941_, v_a_2942_, v_a_2943_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___f_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
lean_inc(v_a_2989_);
v___f_3000_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3000_, 0, v_a_2999_);
lean_closure_set(v___f_3000_, 1, v_fst_2995_);
lean_closure_set(v___f_3000_, 2, v_fst_2996_);
lean_closure_set(v___f_3000_, 3, v_inst_2938_);
lean_closure_set(v___f_3000_, 4, v_a_2989_);
lean_closure_set(v___f_3000_, 5, v_projInfo_x3f_2939_);
v___x_3001_ = 0;
v___x_3002_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2989_, v___f_3000_, v___x_3001_, v___x_3001_, v___x_2987_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec_ref(v___x_2987_);
return v___x_3002_;
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_fst_2996_);
lean_dec(v_fst_2995_);
lean_dec(v_a_2989_);
lean_dec_ref(v___x_2987_);
lean_dec(v_projInfo_x3f_2939_);
lean_dec_ref(v_inst_2938_);
v_a_3003_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2998_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2998_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_a_2989_);
lean_dec_ref(v___x_2987_);
lean_dec(v_projInfo_x3f_2939_);
lean_dec_ref(v_inst_2938_);
v_a_3011_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2992_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2992_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v___x_2987_);
lean_dec(v_projInfo_x3f_2939_);
lean_dec_ref(v_inst_2938_);
v_a_3019_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2988_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2988_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3029_, lean_object* v_projInfo_x3f_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3029_, v_projInfo_x3f_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3037_, lean_object* v___x_3038_, lean_object* v_a_3039_, lean_object* v_inst_3040_, lean_object* v_R_3041_, lean_object* v_a_3042_, lean_object* v_b_3043_, lean_object* v_c_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3037_, v___x_3038_, v_a_3039_, v_a_3042_, v_b_3043_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3051_, lean_object* v___x_3052_, lean_object* v_a_3053_, lean_object* v_inst_3054_, lean_object* v_R_3055_, lean_object* v_a_3056_, lean_object* v_b_3057_, lean_object* v_c_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3051_, v___x_3052_, v_a_3053_, v_inst_3054_, v_R_3055_, v_a_3056_, v_b_3057_, v_c_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_a_3053_);
lean_dec(v___x_3052_);
lean_dec(v_upperBound_3051_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3065_, lean_object* v_msg_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3073_, lean_object* v_msg_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3073_, v_msg_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3081_, lean_object* v_argVars_3082_, lean_object* v_inst_3083_, lean_object* v_a_3084_, lean_object* v_projInfo_x3f_3085_, lean_object* v_inst_3086_, lean_object* v_a_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3081_, v_argVars_3082_, v_inst_3083_, v_a_3084_, v_projInfo_x3f_3085_, v_a_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3094_, lean_object* v_argVars_3095_, lean_object* v_inst_3096_, lean_object* v_a_3097_, lean_object* v_projInfo_x3f_3098_, lean_object* v_inst_3099_, lean_object* v_a_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3094_, v_argVars_3095_, v_inst_3096_, v_a_3097_, v_projInfo_x3f_3098_, v_inst_3099_, v_a_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v_projInfo_x3f_3098_);
return v_res_3106_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v___x_3107_, lean_object* v_as_3108_, size_t v_i_3109_, size_t v_stop_3110_){
_start:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_usize_dec_eq(v_i_3109_, v_stop_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = lean_array_uget_borrowed(v_as_3108_, v_i_3109_);
v___x_3113_ = l_Lean_Expr_containsFVar(v___x_3112_, v___x_3107_);
if (v___x_3113_ == 0)
{
size_t v___x_3114_; size_t v___x_3115_; 
v___x_3114_ = ((size_t)1ULL);
v___x_3115_ = lean_usize_add(v_i_3109_, v___x_3114_);
v_i_3109_ = v___x_3115_;
goto _start;
}
else
{
return v___x_3113_;
}
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = 0;
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v___x_3118_, lean_object* v_as_3119_, lean_object* v_i_3120_, lean_object* v_stop_3121_){
_start:
{
size_t v_i_boxed_3122_; size_t v_stop_boxed_3123_; uint8_t v_res_3124_; lean_object* v_r_3125_; 
v_i_boxed_3122_ = lean_unbox_usize(v_i_3120_);
lean_dec(v_i_3120_);
v_stop_boxed_3123_ = lean_unbox_usize(v_stop_3121_);
lean_dec(v_stop_3121_);
v_res_3124_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(v___x_3118_, v_as_3119_, v_i_boxed_3122_, v_stop_boxed_3123_);
lean_dec_ref(v_as_3119_);
lean_dec(v___x_3118_);
v_r_3125_ = lean_box(v_res_3124_);
return v_r_3125_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__0));
v___x_3128_ = l_Lean_stringToMessageData(v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object* v_ty_3129_, lean_object* v_a_3130_, lean_object* v_as_3131_, size_t v_i_3132_, size_t v_stop_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_a_3141_; uint8_t v___x_3145_; 
v___x_3145_ = lean_usize_dec_eq(v_i_3132_, v_stop_3133_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v_fst_3147_; lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3202_; 
v___x_3146_ = lean_array_uget(v_as_3131_, v_i_3132_);
v_fst_3147_ = lean_ctor_get(v___x_3146_, 0);
v_snd_3148_ = lean_ctor_get(v___x_3146_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3150_ = v___x_3146_;
v_isShared_3151_ = v_isSharedCheck_3202_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_inc(v_fst_3147_);
lean_dec(v___x_3146_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3202_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = l_Lean_Expr_fvarId_x21(v_fst_3147_);
lean_inc(v___x_3152_);
v___x_3153_ = l_Lean_FVarId_getDecl___redArg(v___x_3152_, v___y_3135_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; uint8_t v___y_3156_; uint8_t v___x_3175_; uint8_t v___x_3176_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3153_);
v___x_3175_ = l_Lean_LocalDecl_binderInfo(v_a_3154_);
lean_dec(v_a_3154_);
v___x_3176_ = l_Lean_BinderInfo_isInstImplicit(v___x_3175_);
if (v___x_3176_ == 0)
{
uint8_t v___x_3177_; 
v___x_3177_ = l_Lean_Expr_containsFVar(v_ty_3129_, v___x_3152_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v_array_3182_; lean_object* v_start_3183_; lean_object* v_stop_3184_; lean_object* v___y_3186_; uint8_t v___x_3191_; 
v___x_3178_ = lean_unsigned_to_nat(1u);
v___x_3179_ = lean_nat_add(v_snd_3148_, v___x_3178_);
lean_dec(v_snd_3148_);
v___x_3180_ = lean_array_get_size(v_a_3130_);
lean_inc_ref(v_a_3130_);
v___x_3181_ = l_Array_toSubarray___redArg(v_a_3130_, v___x_3179_, v___x_3180_);
v_array_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_ref(v_array_3182_);
v_start_3183_ = lean_ctor_get(v___x_3181_, 1);
lean_inc(v_start_3183_);
v_stop_3184_ = lean_ctor_get(v___x_3181_, 2);
lean_inc(v_stop_3184_);
lean_dec_ref(v___x_3181_);
v___x_3191_ = lean_nat_dec_lt(v_start_3183_, v_stop_3184_);
if (v___x_3191_ == 0)
{
lean_dec(v_stop_3184_);
lean_dec(v_start_3183_);
lean_dec_ref(v_array_3182_);
lean_dec(v___x_3152_);
v___y_3156_ = v___x_3177_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_array_get_size(v_array_3182_);
v___x_3193_ = lean_nat_dec_le(v_stop_3184_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_dec(v_stop_3184_);
v___y_3186_ = v___x_3192_;
goto v___jp_3185_;
}
else
{
v___y_3186_ = v_stop_3184_;
goto v___jp_3185_;
}
}
v___jp_3185_:
{
uint8_t v___x_3187_; 
v___x_3187_ = lean_nat_dec_lt(v_start_3183_, v___y_3186_);
if (v___x_3187_ == 0)
{
lean_dec(v___y_3186_);
lean_dec(v_start_3183_);
lean_dec_ref(v_array_3182_);
lean_dec(v___x_3152_);
v___y_3156_ = v___x_3177_;
goto v___jp_3155_;
}
else
{
size_t v___x_3188_; size_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3188_ = lean_usize_of_nat(v_start_3183_);
lean_dec(v_start_3183_);
v___x_3189_ = lean_usize_of_nat(v___y_3186_);
lean_dec(v___y_3186_);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(v___x_3152_, v_array_3182_, v___x_3188_, v___x_3189_);
lean_dec_ref(v_array_3182_);
lean_dec(v___x_3152_);
v___y_3156_ = v___x_3190_;
goto v___jp_3155_;
}
}
}
else
{
lean_dec(v___x_3152_);
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
lean_dec(v_fst_3147_);
v_a_3141_ = v_b_3134_;
goto v___jp_3140_;
}
}
else
{
lean_dec(v___x_3152_);
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
lean_dec(v_fst_3147_);
v_a_3141_ = v_b_3134_;
goto v___jp_3140_;
}
v___jp_3155_:
{
if (v___y_3156_ == 0)
{
lean_object* v___x_3157_; 
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
lean_inc(v_fst_3147_);
v___x_3157_ = lean_infer_type(v_fst_3147_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = l_Lean_MessageData_ofExpr(v_fst_3147_);
v___x_3160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1);
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 7);
lean_ctor_set(v___x_3150_, 1, v___x_3160_);
lean_ctor_set(v___x_3150_, 0, v___x_3159_);
v___x_3162_ = v___x_3150_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = l_Lean_MessageData_ofExpr(v_a_3158_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_array_push(v_b_3134_, v___x_3164_);
v_a_3141_ = v___x_3165_;
goto v___jp_3140_;
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_del_object(v___x_3150_);
lean_dec(v_fst_3147_);
lean_dec_ref(v_b_3134_);
lean_dec_ref(v_a_3130_);
v_a_3167_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3157_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3157_);
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
else
{
lean_del_object(v___x_3150_);
lean_dec(v_fst_3147_);
v_a_3141_ = v_b_3134_;
goto v___jp_3140_;
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v___x_3152_);
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
lean_dec(v_fst_3147_);
lean_dec_ref(v_b_3134_);
lean_dec_ref(v_a_3130_);
v_a_3194_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3153_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3153_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; 
lean_dec_ref(v_a_3130_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_b_3134_);
return v___x_3203_;
}
v___jp_3140_:
{
size_t v___x_3142_; size_t v___x_3143_; 
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3132_, v___x_3142_);
v_i_3132_ = v___x_3143_;
v_b_3134_ = v_a_3141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object* v_ty_3204_, lean_object* v_a_3205_, lean_object* v_as_3206_, lean_object* v_i_3207_, lean_object* v_stop_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
size_t v_i_boxed_3215_; size_t v_stop_boxed_3216_; lean_object* v_res_3217_; 
v_i_boxed_3215_ = lean_unbox_usize(v_i_3207_);
lean_dec(v_i_3207_);
v_stop_boxed_3216_ = lean_unbox_usize(v_stop_3208_);
lean_dec(v_stop_3208_);
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3204_, v_a_3205_, v_as_3206_, v_i_boxed_3215_, v_stop_boxed_3216_, v_b_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec_ref(v_as_3206_);
lean_dec_ref(v_ty_3204_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_ty_3218_, lean_object* v_a_3219_, lean_object* v_as_3220_, lean_object* v_start_3221_, lean_object* v_stop_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_3229_ = lean_nat_dec_lt(v_start_3221_, v_stop_3222_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
lean_dec_ref(v_a_3219_);
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
return v___x_3230_;
}
else
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = lean_array_get_size(v_as_3220_);
v___x_3232_ = lean_nat_dec_le(v_stop_3222_, v___x_3231_);
if (v___x_3232_ == 0)
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_nat_dec_lt(v_start_3221_, v___x_3231_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref(v_a_3219_);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3228_);
return v___x_3234_;
}
else
{
size_t v___x_3235_; size_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_usize_of_nat(v_start_3221_);
v___x_3236_ = lean_usize_of_nat(v___x_3231_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3218_, v_a_3219_, v_as_3220_, v___x_3235_, v___x_3236_, v___x_3228_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3237_;
}
}
else
{
size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_usize_of_nat(v_start_3221_);
v___x_3239_ = lean_usize_of_nat(v_stop_3222_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3218_, v_a_3219_, v_as_3220_, v___x_3238_, v___x_3239_, v___x_3228_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_ty_3241_, lean_object* v_a_3242_, lean_object* v_as_3243_, lean_object* v_start_3244_, lean_object* v_stop_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_ty_3241_, v_a_3242_, v_as_3243_, v_start_3244_, v_stop_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v_stop_3245_);
lean_dec(v_start_3244_);
lean_dec_ref(v_as_3243_);
lean_dec_ref(v_ty_3241_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(size_t v_sz_3252_, size_t v_i_3253_, lean_object* v_bs_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_bs_3254_);
return v___x_3261_;
}
else
{
lean_object* v_v_3262_; lean_object* v___x_3263_; 
v_v_3262_ = lean_array_uget_borrowed(v_bs_3254_, v_i_3253_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
lean_inc(v___y_3256_);
lean_inc_ref(v___y_3255_);
lean_inc(v_v_3262_);
v___x_3263_ = lean_infer_type(v_v_3262_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; lean_object* v_bs_x27_3266_; size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v_bs_x27_3266_ = lean_array_uset(v_bs_3254_, v_i_3253_, v___x_3265_);
v___x_3267_ = ((size_t)1ULL);
v___x_3268_ = lean_usize_add(v_i_3253_, v___x_3267_);
v___x_3269_ = lean_array_uset(v_bs_x27_3266_, v_i_3253_, v_a_3264_);
v_i_3253_ = v___x_3268_;
v_bs_3254_ = v___x_3269_;
goto _start;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_bs_3254_);
v_a_3271_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3263_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3263_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
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
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_sz_3279_, lean_object* v_i_3280_, lean_object* v_bs_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
size_t v_sz_boxed_3287_; size_t v_i_boxed_3288_; lean_object* v_res_3289_; 
v_sz_boxed_3287_ = lean_unbox_usize(v_sz_3279_);
lean_dec(v_sz_3279_);
v_i_boxed_3288_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_res_3289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_sz_boxed_3287_, v_i_boxed_3288_, v_bs_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1));
v___x_3294_ = l_Lean_MessageData_ofFormat(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v___x_3305_ = l_Lean_MessageData_ofFormat(v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v_c_3306_, lean_object* v_args_3307_, lean_object* v_ty_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
size_t v_sz_3314_; size_t v___x_3315_; lean_object* v___x_3316_; 
v_sz_3314_ = lean_array_size(v_args_3307_);
v___x_3315_ = ((size_t)0ULL);
lean_inc_ref(v_args_3307_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_sz_3314_, v___x_3315_, v_args_3307_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3319_ = l_Array_zipIdx___redArg(v_args_3307_, v___x_3318_);
lean_dec_ref(v_args_3307_);
v___x_3320_ = lean_array_get_size(v___x_3319_);
v___x_3321_ = l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_ty_3308_, v_a_3317_, v___x_3319_, v___x_3318_, v___x_3320_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec_ref(v___x_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3344_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3344_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3344_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3326_ = lean_array_get_size(v_a_3322_);
v___x_3327_ = lean_nat_dec_eq(v___x_3326_, v___x_3318_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_del_object(v___x_3324_);
v___x_3328_ = lean_array_to_list(v_a_3322_);
v___x_3329_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2);
v___x_3330_ = l_Lean_MessageData_joinSep(v___x_3328_, v___x_3329_);
v___x_3331_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3332_ = l_Lean_MessageData_ofExpr(v_c_3306_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3330_);
v___x_3337_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3338_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
lean_dec(v_a_3322_);
lean_dec_ref(v_c_3306_);
v___x_3340_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3340_);
v___x_3342_ = v___x_3324_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v_c_3306_);
v_a_3345_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3321_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3321_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_args_3307_);
lean_dec_ref(v_c_3306_);
v_a_3353_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3316_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3316_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v_c_3361_, lean_object* v_args_3362_, lean_object* v_ty_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v_c_3361_, v_args_3362_, v_ty_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec_ref(v_ty_3363_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_c_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
lean_inc(v_a_3374_);
lean_inc_ref(v_a_3373_);
lean_inc(v_a_3372_);
lean_inc_ref(v_a_3371_);
lean_inc_ref(v_c_3370_);
v___x_3376_ = lean_infer_type(v_c_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___f_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref(v___x_3376_);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3378_, 0, v_c_3370_);
v___x_3379_ = 0;
v___x_3380_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3377_, v___f_3378_, v___x_3379_, v___x_3379_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3380_;
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v_c_3370_);
v_a_3381_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3376_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3376_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_c_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Meta_checkImpossibleInstance(v_c_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3395_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_declName_3405_, lean_object* v_x_3406_, lean_object* v_target_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
lean_inc_ref(v_target_3407_);
v___x_3413_ = l_Lean_Meta_isClass_x3f(v_target_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3437_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3437_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3437_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
if (lean_obj_tag(v_a_3414_) == 0)
{
uint8_t v___x_3418_; 
v___x_3418_ = l_Lean_Expr_isSorry(v_target_3407_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_del_object(v___x_3416_);
v___x_3419_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3420_ = l_Lean_MessageData_ofName(v_declName_3405_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Lean_MessageData_ofExpr(v_target_3407_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3427_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
lean_dec_ref(v_target_3407_);
lean_dec(v_declName_3405_);
v___x_3429_ = lean_box(0);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3429_);
v___x_3431_ = v___x_3416_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_dec_ref(v_a_3414_);
lean_dec_ref(v_target_3407_);
lean_dec(v_declName_3405_);
v___x_3433_ = lean_box(0);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3433_);
v___x_3435_ = v___x_3416_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_target_3407_);
lean_dec(v_declName_3405_);
v_a_3438_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3413_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3413_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_declName_3446_, lean_object* v_x_3447_, lean_object* v_target_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_declName_3446_, v_x_3447_, v_target_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_x_3447_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_declName_3455_, lean_object* v_c_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v___x_3462_; 
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
v___x_3462_ = lean_infer_type(v_c_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___f_3464_; uint8_t v___x_3465_; lean_object* v___x_3466_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v___f_3464_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3464_, 0, v_declName_3455_);
v___x_3465_ = 0;
v___x_3466_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3463_, v___f_3464_, v___x_3465_, v___x_3465_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
return v___x_3466_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_declName_3455_);
v_a_3467_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3462_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3462_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_declName_3475_, lean_object* v_c_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Meta_checkNonClassInstance(v_declName_3475_, v_c_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; lean_object* v_env_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3486_ = lean_st_ref_get(v___y_3484_);
v_env_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc_ref(v_env_3487_);
lean_dec(v___x_3486_);
v___x_3488_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3487_, v_declName_3483_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3490_, v___y_3491_);
lean_dec(v___y_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3494_, v___y_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3507_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3514_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
lean_ctor_set(v___x_3514_, 2, v___x_3513_);
lean_ctor_set(v___x_3514_, 3, v___x_3513_);
lean_ctor_set(v___x_3514_, 4, v___x_3513_);
lean_ctor_set(v___x_3514_, 5, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3515_, lean_object* v_b_3516_, uint8_t v_kind_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_currNamespace_3522_; lean_object* v___x_3523_; lean_object* v_env_3524_; lean_object* v_nextMacroScope_3525_; lean_object* v_ngen_3526_; lean_object* v_auxDeclNGen_3527_; lean_object* v_traceState_3528_; lean_object* v_messages_3529_; lean_object* v_infoState_3530_; lean_object* v_snapshotTasks_3531_; lean_object* v_newDecls_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3559_; 
v_currNamespace_3522_ = lean_ctor_get(v___y_3519_, 6);
v___x_3523_ = lean_st_ref_take(v___y_3520_);
v_env_3524_ = lean_ctor_get(v___x_3523_, 0);
v_nextMacroScope_3525_ = lean_ctor_get(v___x_3523_, 1);
v_ngen_3526_ = lean_ctor_get(v___x_3523_, 2);
v_auxDeclNGen_3527_ = lean_ctor_get(v___x_3523_, 3);
v_traceState_3528_ = lean_ctor_get(v___x_3523_, 4);
v_messages_3529_ = lean_ctor_get(v___x_3523_, 6);
v_infoState_3530_ = lean_ctor_get(v___x_3523_, 7);
v_snapshotTasks_3531_ = lean_ctor_get(v___x_3523_, 8);
v_newDecls_3532_ = lean_ctor_get(v___x_3523_, 9);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; 
v_unused_3560_ = lean_ctor_get(v___x_3523_, 5);
lean_dec(v_unused_3560_);
v___x_3534_ = v___x_3523_;
v_isShared_3535_ = v_isSharedCheck_3559_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_newDecls_3532_);
lean_inc(v_snapshotTasks_3531_);
lean_inc(v_infoState_3530_);
lean_inc(v_messages_3529_);
lean_inc(v_traceState_3528_);
lean_inc(v_auxDeclNGen_3527_);
lean_inc(v_ngen_3526_);
lean_inc(v_nextMacroScope_3525_);
lean_inc(v_env_3524_);
lean_dec(v___x_3523_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3559_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
lean_inc(v_currNamespace_3522_);
v___x_3536_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3524_, v_ext_3515_, v_b_3516_, v_kind_3517_, v_currNamespace_3522_);
v___x_3537_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 5, v___x_3537_);
lean_ctor_set(v___x_3534_, 0, v___x_3536_);
v___x_3539_ = v___x_3534_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_nextMacroScope_3525_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_ngen_3526_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_auxDeclNGen_3527_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_traceState_3528_);
lean_ctor_set(v_reuseFailAlloc_3558_, 5, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3558_, 6, v_messages_3529_);
lean_ctor_set(v_reuseFailAlloc_3558_, 7, v_infoState_3530_);
lean_ctor_set(v_reuseFailAlloc_3558_, 8, v_snapshotTasks_3531_);
lean_ctor_set(v_reuseFailAlloc_3558_, 9, v_newDecls_3532_);
v___x_3539_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v_mctx_3542_; lean_object* v_zetaDeltaFVarIds_3543_; lean_object* v_postponed_3544_; lean_object* v_diag_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3556_; 
v___x_3540_ = lean_st_ref_set(v___y_3520_, v___x_3539_);
v___x_3541_ = lean_st_ref_take(v___y_3518_);
v_mctx_3542_ = lean_ctor_get(v___x_3541_, 0);
v_zetaDeltaFVarIds_3543_ = lean_ctor_get(v___x_3541_, 2);
v_postponed_3544_ = lean_ctor_get(v___x_3541_, 3);
v_diag_3545_ = lean_ctor_get(v___x_3541_, 4);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v___x_3541_, 1);
lean_dec(v_unused_3557_);
v___x_3547_ = v___x_3541_;
v_isShared_3548_ = v_isSharedCheck_3556_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_diag_3545_);
lean_inc(v_postponed_3544_);
lean_inc(v_zetaDeltaFVarIds_3543_);
lean_inc(v_mctx_3542_);
lean_dec(v___x_3541_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3556_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v___x_3549_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_mctx_3542_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_zetaDeltaFVarIds_3543_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_postponed_3544_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_diag_3545_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_st_ref_set(v___y_3518_, v___x_3551_);
v___x_3553_ = lean_box(0);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3561_, lean_object* v_b_3562_, lean_object* v_kind_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
uint8_t v_kind_boxed_3568_; lean_object* v_res_3569_; 
v_kind_boxed_3568_ = lean_unbox(v_kind_3563_);
v_res_3569_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3561_, v_b_3562_, v_kind_boxed_3568_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3570_, lean_object* v_00_u03b2_3571_, lean_object* v_00_u03c3_3572_, lean_object* v_ext_3573_, lean_object* v_b_3574_, uint8_t v_kind_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3573_, v_b_3574_, v_kind_3575_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_00_u03b2_3583_, lean_object* v_00_u03c3_3584_, lean_object* v_ext_3585_, lean_object* v_b_3586_, lean_object* v_kind_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v_kind_boxed_3593_; lean_object* v_res_3594_; 
v_kind_boxed_3593_ = lean_unbox(v_kind_3587_);
v_res_3594_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3582_, v_00_u03b2_3583_, v_00_u03c3_3584_, v_ext_3585_, v_b_3586_, v_kind_boxed_3593_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; lean_object* v_env_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3598_ = lean_st_ref_get(v___y_3596_);
v_env_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc_ref(v_env_3599_);
lean_dec(v___x_3598_);
v___x_3600_ = lean_get_reducibility_status(v_env_3599_, v_declName_3595_);
v___x_3601_ = lean_box(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3603_, v___y_3604_);
lean_dec(v___y_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3607_, v___y_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
return v___x_3623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
lean_ctor_set(v___x_3626_, 2, v___x_3625_);
lean_ctor_set(v___x_3626_, 3, v___x_3625_);
lean_ctor_set(v___x_3626_, 4, v___x_3624_);
lean_ctor_set(v___x_3626_, 5, v___x_3624_);
lean_ctor_set(v___x_3626_, 6, v___x_3624_);
lean_ctor_set(v___x_3626_, 7, v___x_3624_);
lean_ctor_set(v___x_3626_, 8, v___x_3624_);
lean_ctor_set(v___x_3626_, 9, v___x_3624_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = lean_unsigned_to_nat(32u);
v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3630_ = ((size_t)5ULL);
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = lean_unsigned_to_nat(32u);
v___x_3633_ = lean_mk_empty_array_with_capacity(v___x_3632_);
v___x_3634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3633_);
lean_ctor_set(v___x_3635_, 2, v___x_3631_);
lean_ctor_set(v___x_3635_, 3, v___x_3631_);
lean_ctor_set_usize(v___x_3635_, 4, v___x_3630_);
return v___x_3635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3636_ = lean_box(1);
v___x_3637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3637_);
lean_ctor_set(v___x_3639_, 2, v___x_3636_);
return v___x_3639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3642_ = l_Lean_stringToMessageData(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3645_ = l_Lean_stringToMessageData(v___x_3644_);
return v___x_3645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3654_ = l_Lean_stringToMessageData(v___x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3657_ = l_Lean_stringToMessageData(v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3660_ = l_Lean_stringToMessageData(v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3661_, lean_object* v_declHint_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v_env_3666_; uint8_t v___x_3667_; 
v___x_3665_ = lean_st_ref_get(v___y_3663_);
v_env_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc_ref(v_env_3666_);
lean_dec(v___x_3665_);
v___x_3667_ = l_Lean_Name_isAnonymous(v_declHint_3662_);
if (v___x_3667_ == 0)
{
uint8_t v_isExporting_3668_; 
v_isExporting_3668_ = lean_ctor_get_uint8(v_env_3666_, sizeof(void*)*8);
if (v_isExporting_3668_ == 0)
{
lean_object* v___x_3669_; 
lean_dec_ref(v_env_3666_);
lean_dec(v_declHint_3662_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v_msg_3661_);
return v___x_3669_;
}
else
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
lean_inc_ref(v_env_3666_);
v___x_3670_ = l_Lean_Environment_setExporting(v_env_3666_, v___x_3667_);
lean_inc(v_declHint_3662_);
lean_inc_ref(v___x_3670_);
v___x_3671_ = l_Lean_Environment_contains(v___x_3670_, v_declHint_3662_, v_isExporting_3668_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec_ref(v___x_3670_);
lean_dec_ref(v_env_3666_);
lean_dec(v_declHint_3662_);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_msg_3661_);
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v_c_3678_; lean_object* v___x_3679_; 
v___x_3673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3674_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3675_ = l_Lean_Options_empty;
v___x_3676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3670_);
lean_ctor_set(v___x_3676_, 1, v___x_3673_);
lean_ctor_set(v___x_3676_, 2, v___x_3674_);
lean_ctor_set(v___x_3676_, 3, v___x_3675_);
lean_inc(v_declHint_3662_);
v___x_3677_ = l_Lean_MessageData_ofConstName(v_declHint_3662_, v___x_3667_);
v_c_3678_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3678_, 0, v___x_3676_);
lean_ctor_set(v_c_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3666_, v_declHint_3662_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec_ref(v_env_3666_);
lean_dec(v_declHint_3662_);
v___x_3680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v_c_3678_);
v___x_3682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_MessageData_note(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_msg_3661_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
return v___x_3686_;
}
else
{
lean_object* v_val_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3722_; 
v_val_3687_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3689_ = v___x_3679_;
v_isShared_3690_ = v_isSharedCheck_3722_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_val_3687_);
lean_dec(v___x_3679_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3722_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_mod_3694_; uint8_t v___x_3695_; 
v___x_3691_ = lean_box(0);
v___x_3692_ = l_Lean_Environment_header(v_env_3666_);
lean_dec_ref(v_env_3666_);
v___x_3693_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3692_);
v_mod_3694_ = lean_array_get(v___x_3691_, v___x_3693_, v_val_3687_);
lean_dec(v_val_3687_);
lean_dec_ref(v___x_3693_);
v___x_3695_ = l_Lean_isPrivateName(v_declHint_3662_);
lean_dec(v_declHint_3662_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
lean_ctor_set(v___x_3697_, 1, v_c_3678_);
v___x_3698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Lean_MessageData_ofName(v_mod_3694_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_MessageData_note(v___x_3703_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v_msg_3661_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3705_);
v___x_3707_ = v___x_3689_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v_c_3678_);
v___x_3711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_MessageData_ofName(v_mod_3694_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_note(v___x_3716_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_msg_3661_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3718_);
v___x_3720_ = v___x_3689_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3723_; 
lean_dec_ref(v_env_3666_);
lean_dec(v_declHint_3662_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_msg_3661_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3724_, lean_object* v_declHint_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3724_, v_declHint_3725_, v___y_3726_);
lean_dec(v___y_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3729_, lean_object* v_declHint_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3746_; 
v___x_3736_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3729_, v_declHint_3730_, v___y_3734_);
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3746_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3746_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3741_ = l_Lean_unknownIdentifierMessageTag;
v___x_3742_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v_a_3737_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3742_);
v___x_3744_ = v___x_3739_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3747_, lean_object* v_declHint_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3747_, v_declHint_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3755_, lean_object* v_msg_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_fileName_3762_; lean_object* v_fileMap_3763_; lean_object* v_options_3764_; lean_object* v_currRecDepth_3765_; lean_object* v_maxRecDepth_3766_; lean_object* v_ref_3767_; lean_object* v_currNamespace_3768_; lean_object* v_openDecls_3769_; lean_object* v_initHeartbeats_3770_; lean_object* v_maxHeartbeats_3771_; lean_object* v_quotContext_3772_; lean_object* v_currMacroScope_3773_; uint8_t v_diag_3774_; lean_object* v_cancelTk_x3f_3775_; uint8_t v_suppressElabErrors_3776_; lean_object* v_inheritedTraceOptions_3777_; lean_object* v_ref_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_fileName_3762_ = lean_ctor_get(v___y_3759_, 0);
v_fileMap_3763_ = lean_ctor_get(v___y_3759_, 1);
v_options_3764_ = lean_ctor_get(v___y_3759_, 2);
v_currRecDepth_3765_ = lean_ctor_get(v___y_3759_, 3);
v_maxRecDepth_3766_ = lean_ctor_get(v___y_3759_, 4);
v_ref_3767_ = lean_ctor_get(v___y_3759_, 5);
v_currNamespace_3768_ = lean_ctor_get(v___y_3759_, 6);
v_openDecls_3769_ = lean_ctor_get(v___y_3759_, 7);
v_initHeartbeats_3770_ = lean_ctor_get(v___y_3759_, 8);
v_maxHeartbeats_3771_ = lean_ctor_get(v___y_3759_, 9);
v_quotContext_3772_ = lean_ctor_get(v___y_3759_, 10);
v_currMacroScope_3773_ = lean_ctor_get(v___y_3759_, 11);
v_diag_3774_ = lean_ctor_get_uint8(v___y_3759_, sizeof(void*)*14);
v_cancelTk_x3f_3775_ = lean_ctor_get(v___y_3759_, 12);
v_suppressElabErrors_3776_ = lean_ctor_get_uint8(v___y_3759_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3777_ = lean_ctor_get(v___y_3759_, 13);
v_ref_3778_ = l_Lean_replaceRef(v_ref_3755_, v_ref_3767_);
lean_inc_ref(v_inheritedTraceOptions_3777_);
lean_inc(v_cancelTk_x3f_3775_);
lean_inc(v_currMacroScope_3773_);
lean_inc(v_quotContext_3772_);
lean_inc(v_maxHeartbeats_3771_);
lean_inc(v_initHeartbeats_3770_);
lean_inc(v_openDecls_3769_);
lean_inc(v_currNamespace_3768_);
lean_inc(v_maxRecDepth_3766_);
lean_inc(v_currRecDepth_3765_);
lean_inc_ref(v_options_3764_);
lean_inc_ref(v_fileMap_3763_);
lean_inc_ref(v_fileName_3762_);
v___x_3779_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3779_, 0, v_fileName_3762_);
lean_ctor_set(v___x_3779_, 1, v_fileMap_3763_);
lean_ctor_set(v___x_3779_, 2, v_options_3764_);
lean_ctor_set(v___x_3779_, 3, v_currRecDepth_3765_);
lean_ctor_set(v___x_3779_, 4, v_maxRecDepth_3766_);
lean_ctor_set(v___x_3779_, 5, v_ref_3778_);
lean_ctor_set(v___x_3779_, 6, v_currNamespace_3768_);
lean_ctor_set(v___x_3779_, 7, v_openDecls_3769_);
lean_ctor_set(v___x_3779_, 8, v_initHeartbeats_3770_);
lean_ctor_set(v___x_3779_, 9, v_maxHeartbeats_3771_);
lean_ctor_set(v___x_3779_, 10, v_quotContext_3772_);
lean_ctor_set(v___x_3779_, 11, v_currMacroScope_3773_);
lean_ctor_set(v___x_3779_, 12, v_cancelTk_x3f_3775_);
lean_ctor_set(v___x_3779_, 13, v_inheritedTraceOptions_3777_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*14, v_diag_3774_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*14 + 1, v_suppressElabErrors_3776_);
v___x_3780_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3756_, v___y_3757_, v___y_3758_, v___x_3779_, v___y_3760_);
lean_dec_ref(v___x_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3781_, lean_object* v_msg_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3781_, v_msg_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v_ref_3781_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3789_, lean_object* v_msg_3790_, lean_object* v_declHint_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; lean_object* v_a_3798_; lean_object* v___x_3799_; 
v___x_3797_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3790_, v_declHint_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3789_, v_a_3798_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3800_, lean_object* v_msg_3801_, lean_object* v_declHint_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3800_, v_msg_3801_, v_declHint_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v_ref_3800_);
return v_res_3808_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3811_ = l_Lean_stringToMessageData(v___x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3812_, lean_object* v_constName_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; uint8_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3819_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3820_ = 0;
lean_inc(v_constName_3813_);
v___x_3821_ = l_Lean_MessageData_ofConstName(v_constName_3813_, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3819_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3812_, v___x_3824_, v_constName_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3826_, lean_object* v_constName_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3826_, v_constName_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v_ref_3826_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_ref_3840_; lean_object* v___x_3841_; 
v_ref_3840_ = lean_ctor_get(v___y_3837_, 5);
v___x_3841_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3840_, v_constName_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; lean_object* v_env_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; 
v___x_3855_ = lean_st_ref_get(v___y_3853_);
v_env_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc_ref(v_env_3856_);
lean_dec(v___x_3855_);
v___x_3857_ = 0;
lean_inc(v_constName_3849_);
v___x_3858_ = l_Lean_Environment_find_x3f(v_env_3856_, v_constName_3849_, v___x_3857_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3859_;
}
else
{
lean_object* v_val_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_constName_3849_);
v_val_3860_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3858_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_val_3860_);
lean_dec(v___x_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set_tag(v___x_3862_, 0);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_val_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3882_, uint8_t v_suppressElabErrors_3883_, lean_object* v_x_3884_){
_start:
{
if (lean_obj_tag(v_x_3884_) == 1)
{
lean_object* v_pre_3885_; 
v_pre_3885_ = lean_ctor_get(v_x_3884_, 0);
switch(lean_obj_tag(v_pre_3885_))
{
case 1:
{
lean_object* v_pre_3886_; 
v_pre_3886_ = lean_ctor_get(v_pre_3885_, 0);
switch(lean_obj_tag(v_pre_3886_))
{
case 0:
{
lean_object* v_str_3887_; lean_object* v_str_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v_str_3887_ = lean_ctor_get(v_x_3884_, 1);
v_str_3888_ = lean_ctor_get(v_pre_3885_, 1);
v___x_3889_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3890_ = lean_string_dec_eq(v_str_3888_, v___x_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3891_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3892_ = lean_string_dec_eq(v_str_3888_, v___x_3891_);
if (v___x_3892_ == 0)
{
return v___y_3882_;
}
else
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3894_ = lean_string_dec_eq(v_str_3887_, v___x_3893_);
if (v___x_3894_ == 0)
{
return v___y_3882_;
}
else
{
return v_suppressElabErrors_3883_;
}
}
}
else
{
lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3895_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3896_ = lean_string_dec_eq(v_str_3887_, v___x_3895_);
if (v___x_3896_ == 0)
{
return v___y_3882_;
}
else
{
return v_suppressElabErrors_3883_;
}
}
}
case 1:
{
lean_object* v_pre_3897_; 
v_pre_3897_ = lean_ctor_get(v_pre_3886_, 0);
if (lean_obj_tag(v_pre_3897_) == 0)
{
lean_object* v_str_3898_; lean_object* v_str_3899_; lean_object* v_str_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_str_3898_ = lean_ctor_get(v_x_3884_, 1);
v_str_3899_ = lean_ctor_get(v_pre_3885_, 1);
v_str_3900_ = lean_ctor_get(v_pre_3886_, 1);
v___x_3901_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3902_ = lean_string_dec_eq(v_str_3900_, v___x_3901_);
if (v___x_3902_ == 0)
{
return v___y_3882_;
}
else
{
lean_object* v___x_3903_; uint8_t v___x_3904_; 
v___x_3903_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3904_ = lean_string_dec_eq(v_str_3899_, v___x_3903_);
if (v___x_3904_ == 0)
{
return v___y_3882_;
}
else
{
lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3906_ = lean_string_dec_eq(v_str_3898_, v___x_3905_);
if (v___x_3906_ == 0)
{
return v___y_3882_;
}
else
{
return v_suppressElabErrors_3883_;
}
}
}
}
else
{
return v___y_3882_;
}
}
default: 
{
return v___y_3882_;
}
}
}
case 0:
{
lean_object* v_str_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_str_3907_ = lean_ctor_get(v_x_3884_, 1);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3909_ = lean_string_dec_eq(v_str_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
return v___y_3882_;
}
else
{
return v_suppressElabErrors_3883_;
}
}
default: 
{
return v___y_3882_;
}
}
}
else
{
return v___y_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3910_, lean_object* v_suppressElabErrors_3911_, lean_object* v_x_3912_){
_start:
{
uint8_t v___y_8859__boxed_3913_; uint8_t v_suppressElabErrors_boxed_3914_; uint8_t v_res_3915_; lean_object* v_r_3916_; 
v___y_8859__boxed_3913_ = lean_unbox(v___y_3910_);
v_suppressElabErrors_boxed_3914_ = lean_unbox(v_suppressElabErrors_3911_);
v_res_3915_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8859__boxed_3913_, v_suppressElabErrors_boxed_3914_, v_x_3912_);
lean_dec(v_x_3912_);
v_r_3916_ = lean_box(v_res_3915_);
return v_r_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3917_, lean_object* v_msgData_3918_, uint8_t v_severity_3919_, uint8_t v_isSilent_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; uint8_t v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3964_; uint8_t v___y_3965_; uint8_t v___y_3966_; uint8_t v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3989_; uint8_t v___y_3990_; uint8_t v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; uint8_t v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_4000_; uint8_t v___y_4001_; uint8_t v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; uint8_t v___y_4006_; uint8_t v___x_4011_; lean_object* v___y_4013_; uint8_t v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; uint8_t v___y_4018_; uint8_t v___y_4019_; uint8_t v___y_4021_; uint8_t v___x_4036_; 
v___x_4011_ = 2;
v___x_4036_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3919_, v___x_4011_);
if (v___x_4036_ == 0)
{
v___y_4021_ = v___x_4036_;
goto v___jp_4020_;
}
else
{
uint8_t v___x_4037_; 
lean_inc_ref(v_msgData_3918_);
v___x_4037_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3918_);
v___y_4021_ = v___x_4037_;
goto v___jp_4020_;
}
v___jp_3926_:
{
lean_object* v___x_3936_; lean_object* v_currNamespace_3937_; lean_object* v_openDecls_3938_; lean_object* v_env_3939_; lean_object* v_nextMacroScope_3940_; lean_object* v_ngen_3941_; lean_object* v_auxDeclNGen_3942_; lean_object* v_traceState_3943_; lean_object* v_cache_3944_; lean_object* v_messages_3945_; lean_object* v_infoState_3946_; lean_object* v_snapshotTasks_3947_; lean_object* v_newDecls_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3962_; 
v___x_3936_ = lean_st_ref_take(v___y_3935_);
v_currNamespace_3937_ = lean_ctor_get(v___y_3934_, 6);
v_openDecls_3938_ = lean_ctor_get(v___y_3934_, 7);
v_env_3939_ = lean_ctor_get(v___x_3936_, 0);
v_nextMacroScope_3940_ = lean_ctor_get(v___x_3936_, 1);
v_ngen_3941_ = lean_ctor_get(v___x_3936_, 2);
v_auxDeclNGen_3942_ = lean_ctor_get(v___x_3936_, 3);
v_traceState_3943_ = lean_ctor_get(v___x_3936_, 4);
v_cache_3944_ = lean_ctor_get(v___x_3936_, 5);
v_messages_3945_ = lean_ctor_get(v___x_3936_, 6);
v_infoState_3946_ = lean_ctor_get(v___x_3936_, 7);
v_snapshotTasks_3947_ = lean_ctor_get(v___x_3936_, 8);
v_newDecls_3948_ = lean_ctor_get(v___x_3936_, 9);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3950_ = v___x_3936_;
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_newDecls_3948_);
lean_inc(v_snapshotTasks_3947_);
lean_inc(v_infoState_3946_);
lean_inc(v_messages_3945_);
lean_inc(v_cache_3944_);
lean_inc(v_traceState_3943_);
lean_inc(v_auxDeclNGen_3942_);
lean_inc(v_ngen_3941_);
lean_inc(v_nextMacroScope_3940_);
lean_inc(v_env_3939_);
lean_dec(v___x_3936_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
lean_inc(v_openDecls_3938_);
lean_inc(v_currNamespace_3937_);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v_currNamespace_3937_);
lean_ctor_set(v___x_3952_, 1, v_openDecls_3938_);
v___x_3953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___y_3929_);
lean_inc_ref(v___y_3931_);
lean_inc_ref(v___y_3933_);
v___x_3954_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3954_, 0, v___y_3933_);
lean_ctor_set(v___x_3954_, 1, v___y_3932_);
lean_ctor_set(v___x_3954_, 2, v___y_3928_);
lean_ctor_set(v___x_3954_, 3, v___y_3931_);
lean_ctor_set(v___x_3954_, 4, v___x_3953_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*5, v___y_3927_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*5 + 1, v___y_3930_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*5 + 2, v_isSilent_3920_);
v___x_3955_ = l_Lean_MessageLog_add(v___x_3954_, v_messages_3945_);
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 6, v___x_3955_);
v___x_3957_ = v___x_3950_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_env_3939_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_nextMacroScope_3940_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_ngen_3941_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_auxDeclNGen_3942_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v_traceState_3943_);
lean_ctor_set(v_reuseFailAlloc_3961_, 5, v_cache_3944_);
lean_ctor_set(v_reuseFailAlloc_3961_, 6, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3961_, 7, v_infoState_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 8, v_snapshotTasks_3947_);
lean_ctor_set(v_reuseFailAlloc_3961_, 9, v_newDecls_3948_);
v___x_3957_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_st_ref_set(v___y_3935_, v___x_3957_);
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
}
v___jp_3963_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3987_; 
v___x_3972_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3918_);
v___x_3973_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3972_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_inc_ref_n(v___y_3968_, 2);
v___x_3978_ = l_Lean_FileMap_toPosition(v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
v___x_3979_ = l_Lean_FileMap_toPosition(v___y_3968_, v___y_3971_);
lean_dec(v___y_3971_);
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
v___x_3981_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3967_ == 0)
{
lean_del_object(v___x_3976_);
lean_dec_ref(v___y_3964_);
v___y_3927_ = v___y_3965_;
v___y_3928_ = v___x_3980_;
v___y_3929_ = v_a_3974_;
v___y_3930_ = v___y_3966_;
v___y_3931_ = v___x_3981_;
v___y_3932_ = v___x_3978_;
v___y_3933_ = v___y_3970_;
v___y_3934_ = v___y_3923_;
v___y_3935_ = v___y_3924_;
goto v___jp_3926_;
}
else
{
uint8_t v___x_3982_; 
lean_inc(v_a_3974_);
v___x_3982_ = l_Lean_MessageData_hasTag(v___y_3964_, v_a_3974_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
lean_dec_ref(v___x_3980_);
lean_dec_ref(v___x_3978_);
lean_dec(v_a_3974_);
v___x_3983_ = lean_box(0);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_3983_);
v___x_3985_ = v___x_3976_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
else
{
lean_del_object(v___x_3976_);
v___y_3927_ = v___y_3965_;
v___y_3928_ = v___x_3980_;
v___y_3929_ = v_a_3974_;
v___y_3930_ = v___y_3966_;
v___y_3931_ = v___x_3981_;
v___y_3932_ = v___x_3978_;
v___y_3933_ = v___y_3970_;
v___y_3934_ = v___y_3923_;
v___y_3935_ = v___y_3924_;
goto v___jp_3926_;
}
}
}
}
v___jp_3988_:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Syntax_getTailPos_x3f(v___y_3992_, v___y_3990_);
lean_dec(v___y_3992_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_inc(v___y_3996_);
v___y_3964_ = v___y_3989_;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3993_;
v___y_3969_ = v___y_3996_;
v___y_3970_ = v___y_3995_;
v___y_3971_ = v___y_3996_;
goto v___jp_3963_;
}
else
{
lean_object* v_val_3998_; 
v_val_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_val_3998_);
lean_dec_ref(v___x_3997_);
v___y_3964_ = v___y_3989_;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3993_;
v___y_3969_ = v___y_3996_;
v___y_3970_ = v___y_3995_;
v___y_3971_ = v_val_3998_;
goto v___jp_3963_;
}
}
v___jp_3999_:
{
lean_object* v_ref_4007_; lean_object* v___x_4008_; 
v_ref_4007_ = l_Lean_replaceRef(v_ref_3917_, v___y_4004_);
v___x_4008_ = l_Lean_Syntax_getPos_x3f(v_ref_4007_, v___y_4001_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_unsigned_to_nat(0u);
v___y_3989_ = v___y_4000_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4006_;
v___y_3992_ = v_ref_4007_;
v___y_3993_ = v___y_4003_;
v___y_3994_ = v___y_4002_;
v___y_3995_ = v___y_4005_;
v___y_3996_ = v___x_4009_;
goto v___jp_3988_;
}
else
{
lean_object* v_val_4010_; 
v_val_4010_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_val_4010_);
lean_dec_ref(v___x_4008_);
v___y_3989_ = v___y_4000_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4006_;
v___y_3992_ = v_ref_4007_;
v___y_3993_ = v___y_4003_;
v___y_3994_ = v___y_4002_;
v___y_3995_ = v___y_4005_;
v___y_3996_ = v_val_4010_;
goto v___jp_3988_;
}
}
v___jp_4012_:
{
if (v___y_4019_ == 0)
{
v___y_4000_ = v___y_4016_;
v___y_4001_ = v___y_4018_;
v___y_4002_ = v___y_4014_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4015_;
v___y_4005_ = v___y_4017_;
v___y_4006_ = v_severity_3919_;
goto v___jp_3999_;
}
else
{
v___y_4000_ = v___y_4016_;
v___y_4001_ = v___y_4018_;
v___y_4002_ = v___y_4014_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4015_;
v___y_4005_ = v___y_4017_;
v___y_4006_ = v___x_4011_;
goto v___jp_3999_;
}
}
v___jp_4020_:
{
if (v___y_4021_ == 0)
{
lean_object* v_fileName_4022_; lean_object* v_fileMap_4023_; lean_object* v_options_4024_; lean_object* v_ref_4025_; uint8_t v_suppressElabErrors_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___f_4029_; uint8_t v___x_4030_; uint8_t v___x_4031_; 
v_fileName_4022_ = lean_ctor_get(v___y_3923_, 0);
v_fileMap_4023_ = lean_ctor_get(v___y_3923_, 1);
v_options_4024_ = lean_ctor_get(v___y_3923_, 2);
v_ref_4025_ = lean_ctor_get(v___y_3923_, 5);
v_suppressElabErrors_4026_ = lean_ctor_get_uint8(v___y_3923_, sizeof(void*)*14 + 1);
v___x_4027_ = lean_box(v___y_4021_);
v___x_4028_ = lean_box(v_suppressElabErrors_4026_);
v___f_4029_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4029_, 0, v___x_4027_);
lean_closure_set(v___f_4029_, 1, v___x_4028_);
v___x_4030_ = 1;
v___x_4031_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3919_, v___x_4030_);
if (v___x_4031_ == 0)
{
v___y_4013_ = v_fileMap_4023_;
v___y_4014_ = v_suppressElabErrors_4026_;
v___y_4015_ = v_ref_4025_;
v___y_4016_ = v___f_4029_;
v___y_4017_ = v_fileName_4022_;
v___y_4018_ = v___y_4021_;
v___y_4019_ = v___x_4031_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4032_; uint8_t v___x_4033_; 
v___x_4032_ = l_Lean_warningAsError;
v___x_4033_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4024_, v___x_4032_);
v___y_4013_ = v_fileMap_4023_;
v___y_4014_ = v_suppressElabErrors_4026_;
v___y_4015_ = v_ref_4025_;
v___y_4016_ = v___f_4029_;
v___y_4017_ = v_fileName_4022_;
v___y_4018_ = v___y_4021_;
v___y_4019_ = v___x_4033_;
goto v___jp_4012_;
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec_ref(v_msgData_3918_);
v___x_4034_ = lean_box(0);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_4038_, lean_object* v_msgData_4039_, lean_object* v_severity_4040_, lean_object* v_isSilent_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
uint8_t v_severity_boxed_4047_; uint8_t v_isSilent_boxed_4048_; lean_object* v_res_4049_; 
v_severity_boxed_4047_ = lean_unbox(v_severity_4040_);
v_isSilent_boxed_4048_ = lean_unbox(v_isSilent_4041_);
v_res_4049_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_4038_, v_msgData_4039_, v_severity_boxed_4047_, v_isSilent_boxed_4048_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v_ref_4038_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_4050_, uint8_t v_severity_4051_, uint8_t v_isSilent_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_ref_4058_; lean_object* v___x_4059_; 
v_ref_4058_ = lean_ctor_get(v___y_4055_, 5);
v___x_4059_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_4058_, v_msgData_4050_, v_severity_4051_, v_isSilent_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_4060_, lean_object* v_severity_4061_, lean_object* v_isSilent_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
uint8_t v_severity_boxed_4068_; uint8_t v_isSilent_boxed_4069_; lean_object* v_res_4070_; 
v_severity_boxed_4068_ = lean_unbox(v_severity_4061_);
v_isSilent_boxed_4069_ = lean_unbox(v_isSilent_4062_);
v_res_4070_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_4060_, v_severity_boxed_4068_, v_isSilent_boxed_4069_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v___x_4077_; uint8_t v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = 1;
v___x_4078_ = 0;
v___x_4079_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_4071_, v___x_4077_, v___x_4078_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; lean_object* v_env_4094_; uint8_t v___x_4095_; lean_object* v___x_4096_; 
v___x_4093_ = lean_st_ref_get(v___y_4091_);
v_env_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc_ref(v_env_4094_);
lean_dec(v___x_4093_);
v___x_4095_ = 0;
lean_inc(v_constName_4087_);
v___x_4096_ = l_Lean_Environment_findConstVal_x3f(v_env_4094_, v_constName_4087_, v___x_4095_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4097_;
}
else
{
lean_object* v_val_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_constName_4087_);
v_val_4098_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4096_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_val_4098_);
lean_dec(v___x_4096_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set_tag(v___x_4100_, 0);
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_val_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
if (lean_obj_tag(v_a_4113_) == 0)
{
lean_object* v___x_4115_; 
v___x_4115_ = l_List_reverse___redArg(v_a_4114_);
return v___x_4115_;
}
else
{
lean_object* v_head_4116_; lean_object* v_tail_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
v_head_4116_ = lean_ctor_get(v_a_4113_, 0);
v_tail_4117_ = lean_ctor_get(v_a_4113_, 1);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_a_4113_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v_a_4113_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_tail_4117_);
lean_inc(v_head_4116_);
lean_dec(v_a_4113_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4121_ = l_Lean_mkLevelParam(v_head_4116_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 1, v_a_4114_);
lean_ctor_set(v___x_4119_, 0, v___x_4121_);
v___x_4123_ = v___x_4119_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_a_4114_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
v_a_4113_ = v_tail_4117_;
v_a_4114_ = v___x_4123_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; 
lean_inc(v_constName_4127_);
v___x_4133_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4145_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4145_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4145_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v_levelParams_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v_levelParams_4138_ = lean_ctor_get(v_a_4134_, 1);
lean_inc(v_levelParams_4138_);
lean_dec(v_a_4134_);
v___x_4139_ = lean_box(0);
v___x_4140_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4138_, v___x_4139_);
v___x_4141_ = l_Lean_mkConst(v_constName_4127_, v___x_4140_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v___x_4141_);
v___x_4143_ = v___x_4136_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v_constName_4127_);
v_a_4146_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4133_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4133_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4160_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
return v___x_4163_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4166_ = l_Lean_stringToMessageData(v___x_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4167_, uint8_t v_attrKind_4168_, lean_object* v_prio_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; 
lean_inc(v_declName_4167_);
v___x_4175_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4167_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc_n(v_a_4176_, 2);
lean_dec_ref(v___x_4175_);
v___x_4177_ = l_Lean_Meta_checkImpossibleInstance(v_a_4176_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v___x_4178_; 
lean_dec_ref(v___x_4177_);
lean_inc(v_a_4176_);
lean_inc(v_declName_4167_);
v___x_4178_ = l_Lean_Meta_checkNonClassInstance(v_declName_4167_, v_a_4176_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v___x_4179_; 
lean_dec_ref(v___x_4178_);
lean_inc(v_a_4176_);
v___x_4179_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4176_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___x_4208_; lean_object* v_a_4209_; uint8_t v___x_4210_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref(v___x_4179_);
lean_inc(v_declName_4167_);
v___x_4208_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4167_, v_a_4173_);
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref(v___x_4208_);
v___x_4210_ = lean_unbox(v_a_4209_);
lean_dec(v_a_4209_);
switch(v___x_4210_)
{
case 0:
{
v___y_4182_ = v_a_4170_;
v___y_4183_ = v_a_4171_;
v___y_4184_ = v_a_4172_;
v___y_4185_ = v_a_4173_;
goto v___jp_4181_;
}
case 3:
{
v___y_4182_ = v_a_4170_;
v___y_4183_ = v_a_4171_;
v___y_4184_ = v_a_4172_;
v___y_4185_ = v_a_4173_;
goto v___jp_4181_;
}
default: 
{
lean_object* v___x_4211_; 
lean_inc(v_declName_4167_);
v___x_4211_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4167_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; uint8_t v___x_4213_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4211_);
v___x_4213_ = l_Lean_ConstantInfo_isDefinition(v_a_4212_);
lean_dec(v_a_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v_env_4215_; uint8_t v___x_4216_; 
v___x_4214_ = lean_st_ref_get(v_a_4173_);
v_env_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc_ref(v_env_4215_);
lean_dec(v___x_4214_);
lean_inc(v_declName_4167_);
v___x_4216_ = l_Lean_wasOriginallyDefn(v_env_4215_, v_declName_4167_);
if (v___x_4216_ == 0)
{
v___y_4182_ = v_a_4170_;
v___y_4183_ = v_a_4171_;
v___y_4184_ = v_a_4172_;
v___y_4185_ = v_a_4173_;
goto v___jp_4181_;
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4217_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
lean_inc(v_declName_4167_);
v___x_4218_ = l_Lean_MessageData_ofName(v_declName_4167_);
v___x_4219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
v___x_4221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4219_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
v___x_4222_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_4221_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_dec_ref(v___x_4222_);
v___y_4182_ = v_a_4170_;
v___y_4183_ = v_a_4171_;
v___y_4184_ = v_a_4172_;
v___y_4185_ = v_a_4173_;
goto v___jp_4181_;
}
else
{
lean_dec(v_a_4180_);
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
return v___x_4222_;
}
}
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4223_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
lean_inc(v_declName_4167_);
v___x_4224_ = l_Lean_MessageData_ofName(v_declName_4167_);
v___x_4225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4223_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4225_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
v___x_4228_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_4227_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_dec_ref(v___x_4228_);
v___y_4182_ = v_a_4170_;
v___y_4183_ = v_a_4171_;
v___y_4184_ = v_a_4172_;
v___y_4185_ = v_a_4173_;
goto v___jp_4181_;
}
else
{
lean_dec(v_a_4180_);
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
return v___x_4228_;
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_a_4180_);
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
v_a_4229_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4211_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4211_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
v___jp_4181_:
{
lean_object* v___x_4186_; lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4207_; 
lean_inc(v_declName_4167_);
v___x_4186_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4167_, v___y_4185_);
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4207_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4207_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4191_; 
lean_inc(v_a_4176_);
v___x_4191_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4176_, v_a_4187_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; lean_object* v___x_4195_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4190_ == 0)
{
lean_ctor_set_tag(v___x_4189_, 1);
lean_ctor_set(v___x_4189_, 0, v_declName_4167_);
v___x_4195_ = v___x_4189_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_declName_4167_);
v___x_4195_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4196_, 0, v_a_4180_);
lean_ctor_set(v___x_4196_, 1, v_a_4176_);
lean_ctor_set(v___x_4196_, 2, v_prio_4169_);
lean_ctor_set(v___x_4196_, 3, v___x_4195_);
lean_ctor_set(v___x_4196_, 4, v_a_4192_);
lean_ctor_set_uint8(v___x_4196_, sizeof(void*)*5, v_attrKind_4168_);
v___x_4197_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4193_, v___x_4196_, v_attrKind_4168_, v___y_4183_, v___y_4184_, v___y_4185_);
return v___x_4197_;
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_del_object(v___x_4189_);
lean_dec(v_a_4180_);
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
v_a_4199_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4191_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4191_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
v_a_4237_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4179_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4179_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
return v___x_4178_;
}
}
else
{
lean_dec(v_a_4176_);
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
return v___x_4177_;
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec(v_prio_4169_);
lean_dec(v_declName_4167_);
v_a_4245_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4175_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4175_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4253_, lean_object* v_attrKind_4254_, lean_object* v_prio_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
uint8_t v_attrKind_boxed_4261_; lean_object* v_res_4262_; 
v_attrKind_boxed_4261_ = lean_unbox(v_attrKind_4254_);
v_res_4262_ = l_Lean_Meta_addInstance(v_declName_4253_, v_attrKind_boxed_4261_, v_prio_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4263_, lean_object* v_constName_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4271_, lean_object* v_constName_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4271_, v_constName_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4279_, lean_object* v_ref_4280_, lean_object* v_constName_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4280_, v_constName_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_ref_4289_, lean_object* v_constName_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4288_, v_ref_4289_, v_constName_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v_ref_4289_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_4297_, lean_object* v_ref_4298_, lean_object* v_msg_4299_, lean_object* v_declHint_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_4298_, v_msg_4299_, v_declHint_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_ref_4308_, lean_object* v_msg_4309_, lean_object* v_declHint_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_4307_, v_ref_4308_, v_msg_4309_, v_declHint_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v_ref_4308_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_4317_, lean_object* v_declHint_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_4317_, v_declHint_4318_, v___y_4322_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_4325_, lean_object* v_declHint_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_4325_, v_declHint_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_4333_, lean_object* v_ref_4334_, lean_object* v_msg_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_4334_, v_msg_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4342_, lean_object* v_ref_4343_, lean_object* v_msg_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_4342_, v_ref_4343_, v_msg_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v_ref_4343_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4351_, uint8_t v_s_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; lean_object* v_env_4357_; lean_object* v_nextMacroScope_4358_; lean_object* v_ngen_4359_; lean_object* v_auxDeclNGen_4360_; lean_object* v_traceState_4361_; lean_object* v_messages_4362_; lean_object* v_infoState_4363_; lean_object* v_snapshotTasks_4364_; lean_object* v_newDecls_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4394_; 
v___x_4356_ = lean_st_ref_take(v___y_4354_);
v_env_4357_ = lean_ctor_get(v___x_4356_, 0);
v_nextMacroScope_4358_ = lean_ctor_get(v___x_4356_, 1);
v_ngen_4359_ = lean_ctor_get(v___x_4356_, 2);
v_auxDeclNGen_4360_ = lean_ctor_get(v___x_4356_, 3);
v_traceState_4361_ = lean_ctor_get(v___x_4356_, 4);
v_messages_4362_ = lean_ctor_get(v___x_4356_, 6);
v_infoState_4363_ = lean_ctor_get(v___x_4356_, 7);
v_snapshotTasks_4364_ = lean_ctor_get(v___x_4356_, 8);
v_newDecls_4365_ = lean_ctor_get(v___x_4356_, 9);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4394_ == 0)
{
lean_object* v_unused_4395_; 
v_unused_4395_ = lean_ctor_get(v___x_4356_, 5);
lean_dec(v_unused_4395_);
v___x_4367_ = v___x_4356_;
v_isShared_4368_ = v_isSharedCheck_4394_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_newDecls_4365_);
lean_inc(v_snapshotTasks_4364_);
lean_inc(v_infoState_4363_);
lean_inc(v_messages_4362_);
lean_inc(v_traceState_4361_);
lean_inc(v_auxDeclNGen_4360_);
lean_inc(v_ngen_4359_);
lean_inc(v_nextMacroScope_4358_);
lean_inc(v_env_4357_);
lean_dec(v___x_4356_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4394_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4369_ = 0;
v___x_4370_ = lean_box(0);
v___x_4371_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4357_, v_declName_4351_, v_s_4352_, v___x_4369_, v___x_4370_);
v___x_4372_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 5, v___x_4372_);
lean_ctor_set(v___x_4367_, 0, v___x_4371_);
v___x_4374_ = v___x_4367_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_nextMacroScope_4358_);
lean_ctor_set(v_reuseFailAlloc_4393_, 2, v_ngen_4359_);
lean_ctor_set(v_reuseFailAlloc_4393_, 3, v_auxDeclNGen_4360_);
lean_ctor_set(v_reuseFailAlloc_4393_, 4, v_traceState_4361_);
lean_ctor_set(v_reuseFailAlloc_4393_, 5, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4393_, 6, v_messages_4362_);
lean_ctor_set(v_reuseFailAlloc_4393_, 7, v_infoState_4363_);
lean_ctor_set(v_reuseFailAlloc_4393_, 8, v_snapshotTasks_4364_);
lean_ctor_set(v_reuseFailAlloc_4393_, 9, v_newDecls_4365_);
v___x_4374_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_mctx_4377_; lean_object* v_zetaDeltaFVarIds_4378_; lean_object* v_postponed_4379_; lean_object* v_diag_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4391_; 
v___x_4375_ = lean_st_ref_set(v___y_4354_, v___x_4374_);
v___x_4376_ = lean_st_ref_take(v___y_4353_);
v_mctx_4377_ = lean_ctor_get(v___x_4376_, 0);
v_zetaDeltaFVarIds_4378_ = lean_ctor_get(v___x_4376_, 2);
v_postponed_4379_ = lean_ctor_get(v___x_4376_, 3);
v_diag_4380_ = lean_ctor_get(v___x_4376_, 4);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4391_ == 0)
{
lean_object* v_unused_4392_; 
v_unused_4392_ = lean_ctor_get(v___x_4376_, 1);
lean_dec(v_unused_4392_);
v___x_4382_ = v___x_4376_;
v_isShared_4383_ = v_isSharedCheck_4391_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_diag_4380_);
lean_inc(v_postponed_4379_);
lean_inc(v_zetaDeltaFVarIds_4378_);
lean_inc(v_mctx_4377_);
lean_dec(v___x_4376_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4391_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 1, v___x_4384_);
v___x_4386_ = v___x_4382_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_mctx_4377_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_zetaDeltaFVarIds_4378_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v_postponed_4379_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v_diag_4380_);
v___x_4386_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = lean_st_ref_set(v___y_4353_, v___x_4386_);
v___x_4388_ = lean_box(0);
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
return v___x_4389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4396_, lean_object* v_s_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
uint8_t v_s_boxed_4401_; lean_object* v_res_4402_; 
v_s_boxed_4401_ = lean_unbox(v_s_4397_);
v_res_4402_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4396_, v_s_boxed_4401_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec(v___y_4398_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4403_, uint8_t v_s_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4403_, v_s_4404_, v___y_4406_, v___y_4408_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4411_, lean_object* v_s_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
uint8_t v_s_boxed_4418_; lean_object* v_res_4419_; 
v_s_boxed_4418_ = lean_unbox(v_s_4412_);
v_res_4419_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4411_, v_s_boxed_4418_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4420_, uint8_t v_attrKind_4421_, lean_object* v_prio_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
uint8_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = 3;
lean_inc(v_declName_4420_);
v___x_4429_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4420_, v___x_4428_, v_a_4424_, v_a_4426_);
lean_dec_ref(v___x_4429_);
v___x_4430_ = l_Lean_Meta_addInstance(v_declName_4420_, v_attrKind_4421_, v_prio_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4431_, lean_object* v_attrKind_4432_, lean_object* v_prio_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
uint8_t v_attrKind_boxed_4439_; lean_object* v_res_4440_; 
v_attrKind_boxed_4439_ = lean_unbox(v_attrKind_4432_);
v_res_4440_ = l_Lean_Meta_registerInstance(v_declName_4431_, v_attrKind_boxed_4439_, v_prio_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4441_, lean_object* v_x_4442_){
_start:
{
lean_inc_ref(v_a_4441_);
return v_a_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4443_, lean_object* v_x_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4443_, v_x_4444_);
lean_dec_ref(v_x_4444_);
lean_dec_ref(v_a_4443_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v___x_4450_; lean_object* v_env_4451_; lean_object* v_options_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4450_ = lean_st_ref_get(v___y_4448_);
v_env_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc_ref(v_env_4451_);
lean_dec(v___x_4450_);
v_options_4452_ = lean_ctor_get(v___y_4447_, 2);
v___x_4453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_4454_ = lean_unsigned_to_nat(32u);
v___x_4455_ = lean_mk_empty_array_with_capacity(v___x_4454_);
lean_dec_ref(v___x_4455_);
v___x_4456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_4452_);
v___x_4457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4457_, 0, v_env_4451_);
lean_ctor_set(v___x_4457_, 1, v___x_4453_);
lean_ctor_set(v___x_4457_, 2, v___x_4456_);
lean_ctor_set(v___x_4457_, 3, v_options_4452_);
v___x_4458_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
lean_ctor_set(v___x_4458_, 1, v_msgData_4446_);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_ref_4469_; lean_object* v___x_4470_; lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4479_; 
v_ref_4469_ = lean_ctor_get(v___y_4466_, 5);
v___x_4470_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4465_, v___y_4466_, v___y_4467_);
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4475_; lean_object* v___x_4477_; 
lean_inc(v_ref_4469_);
v___x_4475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4475_, 0, v_ref_4469_);
lean_ctor_set(v___x_4475_, 1, v_a_4471_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 1);
lean_ctor_set(v___x_4473_, 0, v___x_4475_);
v___x_4477_ = v___x_4473_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4485_, lean_object* v_i_4486_, lean_object* v_k_4487_){
_start:
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = lean_array_get_size(v_keys_4485_);
v___x_4489_ = lean_nat_dec_lt(v_i_4486_, v___x_4488_);
if (v___x_4489_ == 0)
{
lean_dec(v_i_4486_);
return v___x_4489_;
}
else
{
lean_object* v_k_x27_4490_; uint8_t v___x_4491_; 
v_k_x27_4490_ = lean_array_fget_borrowed(v_keys_4485_, v_i_4486_);
v___x_4491_ = lean_name_eq(v_k_4487_, v_k_x27_4490_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = lean_unsigned_to_nat(1u);
v___x_4493_ = lean_nat_add(v_i_4486_, v___x_4492_);
lean_dec(v_i_4486_);
v_i_4486_ = v___x_4493_;
goto _start;
}
else
{
lean_dec(v_i_4486_);
return v___x_4491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4495_, lean_object* v_i_4496_, lean_object* v_k_4497_){
_start:
{
uint8_t v_res_4498_; lean_object* v_r_4499_; 
v_res_4498_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4495_, v_i_4496_, v_k_4497_);
lean_dec(v_k_4497_);
lean_dec_ref(v_keys_4495_);
v_r_4499_ = lean_box(v_res_4498_);
return v_r_4499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4500_, size_t v_x_4501_, lean_object* v_x_4502_){
_start:
{
if (lean_obj_tag(v_x_4500_) == 0)
{
lean_object* v_es_4503_; lean_object* v___x_4504_; size_t v___x_4505_; size_t v___x_4506_; size_t v___x_4507_; lean_object* v_j_4508_; lean_object* v___x_4509_; 
v_es_4503_ = lean_ctor_get(v_x_4500_, 0);
v___x_4504_ = lean_box(2);
v___x_4505_ = ((size_t)5ULL);
v___x_4506_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4507_ = lean_usize_land(v_x_4501_, v___x_4506_);
v_j_4508_ = lean_usize_to_nat(v___x_4507_);
v___x_4509_ = lean_array_get_borrowed(v___x_4504_, v_es_4503_, v_j_4508_);
lean_dec(v_j_4508_);
switch(lean_obj_tag(v___x_4509_))
{
case 0:
{
lean_object* v_key_4510_; uint8_t v___x_4511_; 
v_key_4510_ = lean_ctor_get(v___x_4509_, 0);
v___x_4511_ = lean_name_eq(v_x_4502_, v_key_4510_);
return v___x_4511_;
}
case 1:
{
lean_object* v_node_4512_; size_t v___x_4513_; 
v_node_4512_ = lean_ctor_get(v___x_4509_, 0);
v___x_4513_ = lean_usize_shift_right(v_x_4501_, v___x_4505_);
v_x_4500_ = v_node_4512_;
v_x_4501_ = v___x_4513_;
goto _start;
}
default: 
{
uint8_t v___x_4515_; 
v___x_4515_ = 0;
return v___x_4515_;
}
}
}
else
{
lean_object* v_ks_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v_ks_4516_ = lean_ctor_get(v_x_4500_, 0);
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4516_, v___x_4517_, v_x_4502_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4519_, lean_object* v_x_4520_, lean_object* v_x_4521_){
_start:
{
size_t v_x_2362__boxed_4522_; uint8_t v_res_4523_; lean_object* v_r_4524_; 
v_x_2362__boxed_4522_ = lean_unbox_usize(v_x_4520_);
lean_dec(v_x_4520_);
v_res_4523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4519_, v_x_2362__boxed_4522_, v_x_4521_);
lean_dec(v_x_4521_);
lean_dec_ref(v_x_4519_);
v_r_4524_ = lean_box(v_res_4523_);
return v_r_4524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4525_, lean_object* v_x_4526_){
_start:
{
uint64_t v___y_4528_; 
if (lean_obj_tag(v_x_4526_) == 0)
{
uint64_t v___x_4531_; 
v___x_4531_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4528_ = v___x_4531_;
goto v___jp_4527_;
}
else
{
uint64_t v_hash_4532_; 
v_hash_4532_ = lean_ctor_get_uint64(v_x_4526_, sizeof(void*)*2);
v___y_4528_ = v_hash_4532_;
goto v___jp_4527_;
}
v___jp_4527_:
{
size_t v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = lean_uint64_to_usize(v___y_4528_);
v___x_4530_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4525_, v___x_4529_, v_x_4526_);
return v___x_4530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4533_, lean_object* v_x_4534_){
_start:
{
uint8_t v_res_4535_; lean_object* v_r_4536_; 
v_res_4535_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4533_, v_x_4534_);
lean_dec(v_x_4534_);
lean_dec_ref(v_x_4533_);
v_r_4536_ = lean_box(v_res_4535_);
return v_r_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4537_, lean_object* v_declName_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_instanceNames_4545_; uint8_t v___x_4546_; 
v_instanceNames_4545_ = lean_ctor_get(v_d_4537_, 1);
v___x_4546_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4545_, v_declName_4538_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v_d_4537_);
v___x_4547_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4548_ = l_Lean_MessageData_ofConstName(v_declName_4538_, v___x_4546_);
v___x_4549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4547_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
v___x_4550_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4551_, v___y_4539_, v___y_4540_);
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
else
{
goto v___jp_4542_;
}
v___jp_4542_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = l_Lean_Meta_Instances_eraseCore(v_d_4537_, v_declName_4538_);
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
return v___x_4544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4561_, lean_object* v_declName_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4561_, v_declName_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4567_, lean_object* v_declName_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___x_4572_; lean_object* v_env_4573_; lean_object* v___x_4574_; lean_object* v_ext_4575_; lean_object* v_toEnvExtension_4576_; lean_object* v_asyncMode_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4572_ = lean_st_ref_get(v___y_4570_);
v_env_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc_ref(v_env_4573_);
lean_dec(v___x_4572_);
v___x_4574_ = l_Lean_Meta_instanceExtension;
v_ext_4575_ = lean_ctor_get(v___x_4574_, 1);
v_toEnvExtension_4576_ = lean_ctor_get(v_ext_4575_, 0);
v_asyncMode_4577_ = lean_ctor_get(v_toEnvExtension_4576_, 2);
v___x_4578_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4567_, v___x_4574_, v_env_4573_, v_asyncMode_4577_);
v___x_4579_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4578_, v_declName_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4610_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4582_ = v___x_4579_;
v_isShared_4583_ = v_isSharedCheck_4610_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4579_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4610_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v_env_4585_; lean_object* v_nextMacroScope_4586_; lean_object* v_ngen_4587_; lean_object* v_auxDeclNGen_4588_; lean_object* v_traceState_4589_; lean_object* v_messages_4590_; lean_object* v_infoState_4591_; lean_object* v_snapshotTasks_4592_; lean_object* v_newDecls_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4608_; 
v___x_4584_ = lean_st_ref_take(v___y_4570_);
v_env_4585_ = lean_ctor_get(v___x_4584_, 0);
v_nextMacroScope_4586_ = lean_ctor_get(v___x_4584_, 1);
v_ngen_4587_ = lean_ctor_get(v___x_4584_, 2);
v_auxDeclNGen_4588_ = lean_ctor_get(v___x_4584_, 3);
v_traceState_4589_ = lean_ctor_get(v___x_4584_, 4);
v_messages_4590_ = lean_ctor_get(v___x_4584_, 6);
v_infoState_4591_ = lean_ctor_get(v___x_4584_, 7);
v_snapshotTasks_4592_ = lean_ctor_get(v___x_4584_, 8);
v_newDecls_4593_ = lean_ctor_get(v___x_4584_, 9);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4608_ == 0)
{
lean_object* v_unused_4609_; 
v_unused_4609_ = lean_ctor_get(v___x_4584_, 5);
lean_dec(v_unused_4609_);
v___x_4595_ = v___x_4584_;
v_isShared_4596_ = v_isSharedCheck_4608_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_newDecls_4593_);
lean_inc(v_snapshotTasks_4592_);
lean_inc(v_infoState_4591_);
lean_inc(v_messages_4590_);
lean_inc(v_traceState_4589_);
lean_inc(v_auxDeclNGen_4588_);
lean_inc(v_ngen_4587_);
lean_inc(v_nextMacroScope_4586_);
lean_inc(v_env_4585_);
lean_dec(v___x_4584_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4608_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___f_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___f_4597_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4597_, 0, v_a_4580_);
v___x_4598_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4574_, v_env_4585_, v___f_4597_);
v___x_4599_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 5, v___x_4599_);
lean_ctor_set(v___x_4595_, 0, v___x_4598_);
v___x_4601_ = v___x_4595_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_nextMacroScope_4586_);
lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_ngen_4587_);
lean_ctor_set(v_reuseFailAlloc_4607_, 3, v_auxDeclNGen_4588_);
lean_ctor_set(v_reuseFailAlloc_4607_, 4, v_traceState_4589_);
lean_ctor_set(v_reuseFailAlloc_4607_, 5, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4607_, 6, v_messages_4590_);
lean_ctor_set(v_reuseFailAlloc_4607_, 7, v_infoState_4591_);
lean_ctor_set(v_reuseFailAlloc_4607_, 8, v_snapshotTasks_4592_);
lean_ctor_set(v_reuseFailAlloc_4607_, 9, v_newDecls_4593_);
v___x_4601_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4602_ = lean_st_ref_set(v___y_4570_, v___x_4601_);
v___x_4603_ = lean_box(0);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 0, v___x_4603_);
v___x_4605_ = v___x_4582_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_a_4611_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4579_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4579_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4619_, lean_object* v_declName_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4619_, v_declName_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec_ref(v___x_4619_);
return v_res_4624_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4631_; uint64_t v___x_4632_; 
v___x_4631_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4631_);
return v___x_4632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4634_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4635_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
lean_ctor_set_uint64(v___x_4635_, sizeof(void*)*1, v___x_4633_);
return v___x_4635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
lean_ctor_set(v___x_4640_, 2, v___x_4639_);
lean_ctor_set(v___x_4640_, 3, v___x_4639_);
lean_ctor_set(v___x_4640_, 4, v___x_4639_);
lean_ctor_set(v___x_4640_, 5, v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
lean_ctor_set(v___x_4642_, 2, v___x_4641_);
lean_ctor_set(v___x_4642_, 3, v___x_4641_);
lean_ctor_set(v___x_4642_, 4, v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4643_, lean_object* v___x_4644_, lean_object* v_declName_4645_, lean_object* v_stx_4646_, uint8_t v_attrKind_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = lean_unsigned_to_nat(1u);
v___x_4652_ = l_Lean_Syntax_getArg(v_stx_4646_, v___x_4651_);
v___x_4653_ = l_Lean_getAttrParamOptPrio(v___x_4652_, v___y_4648_, v___y_4649_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; uint8_t v___x_4655_; uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; size_t v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = 0;
v___x_4656_ = 1;
v___x_4657_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4658_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4659_ = lean_unsigned_to_nat(32u);
v___x_4660_ = lean_mk_empty_array_with_capacity(v___x_4659_);
v___x_4661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4662_ = ((size_t)5ULL);
lean_inc_n(v___x_4643_, 6);
v___x_4663_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4663_, 0, v___x_4661_);
lean_ctor_set(v___x_4663_, 1, v___x_4660_);
lean_ctor_set(v___x_4663_, 2, v___x_4643_);
lean_ctor_set(v___x_4663_, 3, v___x_4643_);
lean_ctor_set_usize(v___x_4663_, 4, v___x_4662_);
v___x_4664_ = lean_box(1);
lean_inc_ref(v___x_4663_);
v___x_4665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4658_);
lean_ctor_set(v___x_4665_, 1, v___x_4663_);
lean_ctor_set(v___x_4665_, 2, v___x_4664_);
v___x_4666_ = lean_mk_empty_array_with_capacity(v___x_4643_);
v___x_4667_ = lean_box(0);
lean_inc(v___x_4644_);
v___x_4668_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4668_, 0, v___x_4657_);
lean_ctor_set(v___x_4668_, 1, v___x_4644_);
lean_ctor_set(v___x_4668_, 2, v___x_4665_);
lean_ctor_set(v___x_4668_, 3, v___x_4666_);
lean_ctor_set(v___x_4668_, 4, v___x_4667_);
lean_ctor_set(v___x_4668_, 5, v___x_4643_);
lean_ctor_set(v___x_4668_, 6, v___x_4667_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7, v___x_4655_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 1, v___x_4655_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 2, v___x_4655_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 3, v___x_4656_);
v___x_4669_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4643_);
lean_ctor_set(v___x_4669_, 1, v___x_4643_);
lean_ctor_set(v___x_4669_, 2, v___x_4643_);
lean_ctor_set(v___x_4669_, 3, v___x_4643_);
lean_ctor_set(v___x_4669_, 4, v___x_4658_);
lean_ctor_set(v___x_4669_, 5, v___x_4658_);
lean_ctor_set(v___x_4669_, 6, v___x_4658_);
lean_ctor_set(v___x_4669_, 7, v___x_4658_);
lean_ctor_set(v___x_4669_, 8, v___x_4658_);
lean_ctor_set(v___x_4669_, 9, v___x_4658_);
v___x_4670_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4669_);
lean_ctor_set(v___x_4672_, 1, v___x_4670_);
lean_ctor_set(v___x_4672_, 2, v___x_4644_);
lean_ctor_set(v___x_4672_, 3, v___x_4663_);
lean_ctor_set(v___x_4672_, 4, v___x_4671_);
v___x_4673_ = lean_st_mk_ref(v___x_4672_);
v___x_4674_ = l_Lean_Meta_addInstance(v_declName_4645_, v_attrKind_4647_, v_a_4654_, v___x_4668_, v___x_4673_, v___y_4648_, v___y_4649_);
lean_dec_ref(v___x_4668_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4683_; 
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4683_ == 0)
{
lean_object* v_unused_4684_; 
v_unused_4684_ = lean_ctor_get(v___x_4674_, 0);
lean_dec(v_unused_4684_);
v___x_4676_ = v___x_4674_;
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
else
{
lean_dec(v___x_4674_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = lean_st_ref_get(v___x_4673_);
lean_dec(v___x_4673_);
lean_dec(v___x_4678_);
v___x_4679_ = lean_box(0);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v___x_4679_);
v___x_4681_ = v___x_4676_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
else
{
lean_dec(v___x_4673_);
return v___x_4674_;
}
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_dec(v_declName_4645_);
lean_dec(v___x_4644_);
lean_dec(v___x_4643_);
v_a_4685_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4653_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4653_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4693_, lean_object* v___x_4694_, lean_object* v_declName_4695_, lean_object* v_stx_4696_, lean_object* v_attrKind_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
uint8_t v_attrKind_boxed_4701_; lean_object* v_res_4702_; 
v_attrKind_boxed_4701_ = lean_unbox(v_attrKind_4697_);
v_res_4702_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4693_, v___x_4694_, v_declName_4695_, v_stx_4696_, v_attrKind_boxed_4701_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v_stx_4696_);
return v_res_4702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___f_4704_; 
v___x_4703_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4704_, 0, v___x_4703_);
return v___f_4704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4771_; lean_object* v___f_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___f_4771_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4772_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4773_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
lean_ctor_set(v___x_4774_, 1, v___f_4772_);
lean_ctor_set(v___x_4774_, 2, v___f_4771_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4777_ = l_Lean_registerBuiltinAttribute(v___x_4776_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4780_, lean_object* v_x_4781_, lean_object* v_x_4782_){
_start:
{
uint8_t v___x_4783_; 
v___x_4783_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4781_, v_x_4782_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4784_, lean_object* v_x_4785_, lean_object* v_x_4786_){
_start:
{
uint8_t v_res_4787_; lean_object* v_r_4788_; 
v_res_4787_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4784_, v_x_4785_, v_x_4786_);
lean_dec(v_x_4786_);
lean_dec_ref(v_x_4785_);
v_r_4788_ = lean_box(v_res_4787_);
return v_r_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4789_, lean_object* v_msg_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4790_, v___y_4791_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4795_, lean_object* v_msg_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4795_, v_msg_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
return v_res_4800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4801_, lean_object* v_x_4802_, size_t v_x_4803_, lean_object* v_x_4804_){
_start:
{
uint8_t v___x_4805_; 
v___x_4805_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4802_, v_x_4803_, v_x_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4806_, lean_object* v_x_4807_, lean_object* v_x_4808_, lean_object* v_x_4809_){
_start:
{
size_t v_x_3014__boxed_4810_; uint8_t v_res_4811_; lean_object* v_r_4812_; 
v_x_3014__boxed_4810_ = lean_unbox_usize(v_x_4808_);
lean_dec(v_x_4808_);
v_res_4811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4806_, v_x_4807_, v_x_3014__boxed_4810_, v_x_4809_);
lean_dec(v_x_4809_);
lean_dec_ref(v_x_4807_);
v_r_4812_ = lean_box(v_res_4811_);
return v_r_4812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4813_, lean_object* v_keys_4814_, lean_object* v_vals_4815_, lean_object* v_heq_4816_, lean_object* v_i_4817_, lean_object* v_k_4818_){
_start:
{
uint8_t v___x_4819_; 
v___x_4819_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4814_, v_i_4817_, v_k_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4820_, lean_object* v_keys_4821_, lean_object* v_vals_4822_, lean_object* v_heq_4823_, lean_object* v_i_4824_, lean_object* v_k_4825_){
_start:
{
uint8_t v_res_4826_; lean_object* v_r_4827_; 
v_res_4826_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4820_, v_keys_4821_, v_vals_4822_, v_heq_4823_, v_i_4824_, v_k_4825_);
lean_dec(v_k_4825_);
lean_dec_ref(v_vals_4822_);
lean_dec_ref(v_keys_4821_);
v_r_4827_ = lean_box(v_res_4826_);
return v_r_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4830_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4831_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4832_ = l_Lean_addBuiltinDocString(v___x_4830_, v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4835_){
_start:
{
lean_object* v___x_4837_; lean_object* v_env_4838_; lean_object* v___x_4839_; lean_object* v_ext_4840_; lean_object* v_toEnvExtension_4841_; lean_object* v_asyncMode_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v_discrTree_4845_; lean_object* v___x_4846_; 
v___x_4837_ = lean_st_ref_get(v_a_4835_);
v_env_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc_ref(v_env_4838_);
lean_dec(v___x_4837_);
v___x_4839_ = l_Lean_Meta_instanceExtension;
v_ext_4840_ = lean_ctor_get(v___x_4839_, 1);
v_toEnvExtension_4841_ = lean_ctor_get(v_ext_4840_, 0);
v_asyncMode_4842_ = lean_ctor_get(v_toEnvExtension_4841_, 2);
v___x_4843_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4844_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4843_, v___x_4839_, v_env_4838_, v_asyncMode_4842_);
v_discrTree_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc_ref(v_discrTree_4845_);
lean_dec(v___x_4844_);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v_discrTree_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4847_);
lean_dec(v_a_4847_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4854_, v_a_4855_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4858_){
_start:
{
lean_object* v___x_4860_; lean_object* v_env_4861_; lean_object* v___x_4862_; lean_object* v_ext_4863_; lean_object* v_toEnvExtension_4864_; lean_object* v_asyncMode_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v_erased_4868_; lean_object* v___x_4869_; 
v___x_4860_ = lean_st_ref_get(v_a_4858_);
v_env_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc_ref(v_env_4861_);
lean_dec(v___x_4860_);
v___x_4862_ = l_Lean_Meta_instanceExtension;
v_ext_4863_ = lean_ctor_get(v___x_4862_, 1);
v_toEnvExtension_4864_ = lean_ctor_get(v_ext_4863_, 0);
v_asyncMode_4865_ = lean_ctor_get(v_toEnvExtension_4864_, 2);
v___x_4866_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4867_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4866_, v___x_4862_, v_env_4861_, v_asyncMode_4865_);
v_erased_4868_ = lean_ctor_get(v___x_4867_, 2);
lean_inc_ref(v_erased_4868_);
lean_dec(v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_erased_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4870_);
lean_dec(v_a_4870_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4874_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Meta_getErasedInstances(v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
return v_res_4880_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4881_, lean_object* v_declName_4882_){
_start:
{
lean_object* v___x_4883_; lean_object* v_ext_4884_; lean_object* v_toEnvExtension_4885_; lean_object* v_asyncMode_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v_instanceNames_4889_; uint8_t v___x_4890_; 
v___x_4883_ = l_Lean_Meta_instanceExtension;
v_ext_4884_ = lean_ctor_get(v___x_4883_, 1);
v_toEnvExtension_4885_ = lean_ctor_get(v_ext_4884_, 0);
v_asyncMode_4886_ = lean_ctor_get(v_toEnvExtension_4885_, 2);
v___x_4887_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4888_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4887_, v___x_4883_, v_env_4881_, v_asyncMode_4886_);
v_instanceNames_4889_ = lean_ctor_get(v___x_4888_, 1);
lean_inc_ref(v_instanceNames_4889_);
lean_dec(v___x_4888_);
v___x_4890_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4889_, v_declName_4882_);
lean_dec_ref(v_instanceNames_4889_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4891_, lean_object* v_declName_4892_){
_start:
{
uint8_t v_res_4893_; lean_object* v_r_4894_; 
v_res_4893_ = l_Lean_Meta_isInstanceCore(v_env_4891_, v_declName_4892_);
lean_dec(v_declName_4892_);
v_r_4894_ = lean_box(v_res_4893_);
return v_r_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v___x_4898_; lean_object* v_env_4899_; uint8_t v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4898_ = lean_st_ref_get(v_a_4896_);
v_env_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc_ref(v_env_4899_);
lean_dec(v___x_4898_);
v___x_4900_ = l_Lean_Meta_isInstanceCore(v_env_4899_, v_declName_4895_);
v___x_4901_ = lean_box(v___x_4900_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Lean_Meta_isInstance___redArg(v_declName_4903_, v_a_4904_);
lean_dec(v_a_4904_);
lean_dec(v_declName_4903_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_Meta_isInstance___redArg(v_declName_4907_, v_a_4909_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Meta_isInstance(v_declName_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_declName_4912_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4917_, lean_object* v_vals_4918_, lean_object* v_i_4919_, lean_object* v_k_4920_){
_start:
{
lean_object* v___x_4921_; uint8_t v___x_4922_; 
v___x_4921_ = lean_array_get_size(v_keys_4917_);
v___x_4922_ = lean_nat_dec_lt(v_i_4919_, v___x_4921_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; 
lean_dec(v_i_4919_);
v___x_4923_ = lean_box(0);
return v___x_4923_;
}
else
{
lean_object* v_k_x27_4924_; uint8_t v___x_4925_; 
v_k_x27_4924_ = lean_array_fget_borrowed(v_keys_4917_, v_i_4919_);
v___x_4925_ = lean_name_eq(v_k_4920_, v_k_x27_4924_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_unsigned_to_nat(1u);
v___x_4927_ = lean_nat_add(v_i_4919_, v___x_4926_);
lean_dec(v_i_4919_);
v_i_4919_ = v___x_4927_;
goto _start;
}
else
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = lean_array_fget_borrowed(v_vals_4918_, v_i_4919_);
lean_dec(v_i_4919_);
lean_inc(v___x_4929_);
v___x_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4929_);
return v___x_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4931_, lean_object* v_vals_4932_, lean_object* v_i_4933_, lean_object* v_k_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4931_, v_vals_4932_, v_i_4933_, v_k_4934_);
lean_dec(v_k_4934_);
lean_dec_ref(v_vals_4932_);
lean_dec_ref(v_keys_4931_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4936_, size_t v_x_4937_, lean_object* v_x_4938_){
_start:
{
if (lean_obj_tag(v_x_4936_) == 0)
{
lean_object* v_es_4939_; lean_object* v___x_4940_; size_t v___x_4941_; size_t v___x_4942_; size_t v___x_4943_; lean_object* v_j_4944_; lean_object* v___x_4945_; 
v_es_4939_ = lean_ctor_get(v_x_4936_, 0);
v___x_4940_ = lean_box(2);
v___x_4941_ = ((size_t)5ULL);
v___x_4942_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4943_ = lean_usize_land(v_x_4937_, v___x_4942_);
v_j_4944_ = lean_usize_to_nat(v___x_4943_);
v___x_4945_ = lean_array_get_borrowed(v___x_4940_, v_es_4939_, v_j_4944_);
lean_dec(v_j_4944_);
switch(lean_obj_tag(v___x_4945_))
{
case 0:
{
lean_object* v_key_4946_; lean_object* v_val_4947_; uint8_t v___x_4948_; 
v_key_4946_ = lean_ctor_get(v___x_4945_, 0);
v_val_4947_ = lean_ctor_get(v___x_4945_, 1);
v___x_4948_ = lean_name_eq(v_x_4938_, v_key_4946_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_box(0);
return v___x_4949_;
}
else
{
lean_object* v___x_4950_; 
lean_inc(v_val_4947_);
v___x_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4950_, 0, v_val_4947_);
return v___x_4950_;
}
}
case 1:
{
lean_object* v_node_4951_; size_t v___x_4952_; 
v_node_4951_ = lean_ctor_get(v___x_4945_, 0);
v___x_4952_ = lean_usize_shift_right(v_x_4937_, v___x_4941_);
v_x_4936_ = v_node_4951_;
v_x_4937_ = v___x_4952_;
goto _start;
}
default: 
{
lean_object* v___x_4954_; 
v___x_4954_ = lean_box(0);
return v___x_4954_;
}
}
}
else
{
lean_object* v_ks_4955_; lean_object* v_vs_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v_ks_4955_ = lean_ctor_get(v_x_4936_, 0);
v_vs_4956_ = lean_ctor_get(v_x_4936_, 1);
v___x_4957_ = lean_unsigned_to_nat(0u);
v___x_4958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4955_, v_vs_4956_, v___x_4957_, v_x_4938_);
return v___x_4958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4959_, lean_object* v_x_4960_, lean_object* v_x_4961_){
_start:
{
size_t v_x_490__boxed_4962_; lean_object* v_res_4963_; 
v_x_490__boxed_4962_ = lean_unbox_usize(v_x_4960_);
lean_dec(v_x_4960_);
v_res_4963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4959_, v_x_490__boxed_4962_, v_x_4961_);
lean_dec(v_x_4961_);
lean_dec_ref(v_x_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4964_, lean_object* v_x_4965_){
_start:
{
uint64_t v___y_4967_; 
if (lean_obj_tag(v_x_4965_) == 0)
{
uint64_t v___x_4970_; 
v___x_4970_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4967_ = v___x_4970_;
goto v___jp_4966_;
}
else
{
uint64_t v_hash_4971_; 
v_hash_4971_ = lean_ctor_get_uint64(v_x_4965_, sizeof(void*)*2);
v___y_4967_ = v_hash_4971_;
goto v___jp_4966_;
}
v___jp_4966_:
{
size_t v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = lean_uint64_to_usize(v___y_4967_);
v___x_4969_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4964_, v___x_4968_, v_x_4965_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4972_, lean_object* v_x_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4972_, v_x_4973_);
lean_dec(v_x_4973_);
lean_dec_ref(v_x_4972_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v___x_4978_; lean_object* v_env_4979_; lean_object* v___x_4980_; lean_object* v_ext_4981_; lean_object* v_toEnvExtension_4982_; lean_object* v_asyncMode_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v_instanceNames_4986_; lean_object* v___x_4987_; 
v___x_4978_ = lean_st_ref_get(v_a_4976_);
v_env_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc_ref(v_env_4979_);
lean_dec(v___x_4978_);
v___x_4980_ = l_Lean_Meta_instanceExtension;
v_ext_4981_ = lean_ctor_get(v___x_4980_, 1);
v_toEnvExtension_4982_ = lean_ctor_get(v_ext_4981_, 0);
v_asyncMode_4983_ = lean_ctor_get(v_toEnvExtension_4982_, 2);
v___x_4984_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4985_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4984_, v___x_4980_, v_env_4979_, v_asyncMode_4983_);
v_instanceNames_4986_ = lean_ctor_get(v___x_4985_, 1);
lean_inc_ref(v_instanceNames_4986_);
lean_dec(v___x_4985_);
v___x_4987_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4986_, v_declName_4975_);
lean_dec_ref(v_instanceNames_4986_);
if (lean_obj_tag(v___x_4987_) == 1)
{
lean_object* v_val_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4997_; 
v_val_4988_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4990_ = v___x_4987_;
v_isShared_4991_ = v_isSharedCheck_4997_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_val_4988_);
lean_dec(v___x_4987_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4997_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v_priority_4992_; lean_object* v___x_4994_; 
v_priority_4992_ = lean_ctor_get(v_val_4988_, 2);
lean_inc(v_priority_4992_);
lean_dec(v_val_4988_);
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_priority_4992_);
v___x_4994_ = v___x_4990_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_priority_4992_);
v___x_4994_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
return v___x_4995_;
}
}
}
else
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec(v___x_4987_);
v___x_4998_ = lean_box(0);
v___x_4999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
return v___x_4999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5000_, v_a_5001_);
lean_dec(v_a_5001_);
lean_dec(v_declName_5000_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5004_, v_a_5006_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_declName_5009_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5014_, lean_object* v_x_5015_, lean_object* v_x_5016_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5015_, v_x_5016_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5018_, lean_object* v_x_5019_, lean_object* v_x_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5018_, v_x_5019_, v_x_5020_);
lean_dec(v_x_5020_);
lean_dec_ref(v_x_5019_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5022_, lean_object* v_x_5023_, size_t v_x_5024_, lean_object* v_x_5025_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5023_, v_x_5024_, v_x_5025_);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5027_, lean_object* v_x_5028_, lean_object* v_x_5029_, lean_object* v_x_5030_){
_start:
{
size_t v_x_606__boxed_5031_; lean_object* v_res_5032_; 
v_x_606__boxed_5031_ = lean_unbox_usize(v_x_5029_);
lean_dec(v_x_5029_);
v_res_5032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5027_, v_x_5028_, v_x_606__boxed_5031_, v_x_5030_);
lean_dec(v_x_5030_);
lean_dec_ref(v_x_5028_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5033_, lean_object* v_keys_5034_, lean_object* v_vals_5035_, lean_object* v_heq_5036_, lean_object* v_i_5037_, lean_object* v_k_5038_){
_start:
{
lean_object* v___x_5039_; 
v___x_5039_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5034_, v_vals_5035_, v_i_5037_, v_k_5038_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5040_, lean_object* v_keys_5041_, lean_object* v_vals_5042_, lean_object* v_heq_5043_, lean_object* v_i_5044_, lean_object* v_k_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5040_, v_keys_5041_, v_vals_5042_, v_heq_5043_, v_i_5044_, v_k_5045_);
lean_dec(v_k_5045_);
lean_dec_ref(v_vals_5042_);
lean_dec_ref(v_keys_5041_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v___x_5050_; lean_object* v_env_5051_; lean_object* v___x_5052_; lean_object* v_ext_5053_; lean_object* v_toEnvExtension_5054_; lean_object* v_asyncMode_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v_instanceNames_5058_; lean_object* v___x_5059_; 
v___x_5050_ = lean_st_ref_get(v_a_5048_);
v_env_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc_ref(v_env_5051_);
lean_dec(v___x_5050_);
v___x_5052_ = l_Lean_Meta_instanceExtension;
v_ext_5053_ = lean_ctor_get(v___x_5052_, 1);
v_toEnvExtension_5054_ = lean_ctor_get(v_ext_5053_, 0);
v_asyncMode_5055_ = lean_ctor_get(v_toEnvExtension_5054_, 2);
v___x_5056_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5057_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5056_, v___x_5052_, v_env_5051_, v_asyncMode_5055_);
v_instanceNames_5058_ = lean_ctor_get(v___x_5057_, 1);
lean_inc_ref(v_instanceNames_5058_);
lean_dec(v___x_5057_);
v___x_5059_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5058_, v_declName_5047_);
lean_dec_ref(v_instanceNames_5058_);
if (lean_obj_tag(v___x_5059_) == 1)
{
lean_object* v_val_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5070_; 
v_val_5060_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5062_ = v___x_5059_;
v_isShared_5063_ = v_isSharedCheck_5070_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_val_5060_);
lean_dec(v___x_5059_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5070_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
uint8_t v_attrKind_5064_; lean_object* v___x_5065_; lean_object* v___x_5067_; 
v_attrKind_5064_ = lean_ctor_get_uint8(v_val_5060_, sizeof(void*)*5);
lean_dec(v_val_5060_);
v___x_5065_ = lean_box(v_attrKind_5064_);
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 0, v___x_5065_);
v___x_5067_ = v___x_5062_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
lean_object* v___x_5068_; 
v___x_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
return v___x_5068_;
}
}
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
lean_dec(v___x_5059_);
v___x_5071_ = lean_box(0);
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
return v___x_5072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5073_, v_a_5074_);
lean_dec(v_a_5074_);
lean_dec(v_declName_5073_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5077_, v_a_5079_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5082_, v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_declName_5082_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5091_, lean_object* v_v_5092_, lean_object* v_t_5093_){
_start:
{
if (lean_obj_tag(v_t_5093_) == 0)
{
lean_object* v_size_5094_; lean_object* v_k_5095_; lean_object* v_v_5096_; lean_object* v_l_5097_; lean_object* v_r_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5379_; 
v_size_5094_ = lean_ctor_get(v_t_5093_, 0);
v_k_5095_ = lean_ctor_get(v_t_5093_, 1);
v_v_5096_ = lean_ctor_get(v_t_5093_, 2);
v_l_5097_ = lean_ctor_get(v_t_5093_, 3);
v_r_5098_ = lean_ctor_get(v_t_5093_, 4);
v_isSharedCheck_5379_ = !lean_is_exclusive(v_t_5093_);
if (v_isSharedCheck_5379_ == 0)
{
v___x_5100_ = v_t_5093_;
v_isShared_5101_ = v_isSharedCheck_5379_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_r_5098_);
lean_inc(v_l_5097_);
lean_inc(v_v_5096_);
lean_inc(v_k_5095_);
lean_inc(v_size_5094_);
lean_dec(v_t_5093_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5379_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
uint8_t v___x_5102_; 
v___x_5102_ = lean_nat_dec_lt(v_k_5095_, v_k_5091_);
if (v___x_5102_ == 0)
{
uint8_t v___x_5103_; 
v___x_5103_ = lean_nat_dec_eq(v_k_5095_, v_k_5091_);
if (v___x_5103_ == 0)
{
lean_object* v_impl_5104_; lean_object* v___x_5105_; 
lean_dec(v_size_5094_);
v_impl_5104_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5091_, v_v_5092_, v_r_5098_);
v___x_5105_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5097_) == 0)
{
lean_object* v_size_5106_; lean_object* v_size_5107_; lean_object* v_k_5108_; lean_object* v_v_5109_; lean_object* v_l_5110_; lean_object* v_r_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
v_size_5106_ = lean_ctor_get(v_l_5097_, 0);
v_size_5107_ = lean_ctor_get(v_impl_5104_, 0);
lean_inc(v_size_5107_);
v_k_5108_ = lean_ctor_get(v_impl_5104_, 1);
lean_inc(v_k_5108_);
v_v_5109_ = lean_ctor_get(v_impl_5104_, 2);
lean_inc(v_v_5109_);
v_l_5110_ = lean_ctor_get(v_impl_5104_, 3);
lean_inc(v_l_5110_);
v_r_5111_ = lean_ctor_get(v_impl_5104_, 4);
lean_inc(v_r_5111_);
v___x_5112_ = lean_unsigned_to_nat(3u);
v___x_5113_ = lean_nat_mul(v___x_5112_, v_size_5106_);
v___x_5114_ = lean_nat_dec_lt(v___x_5113_, v_size_5107_);
lean_dec(v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
lean_dec(v_r_5111_);
lean_dec(v_l_5110_);
lean_dec(v_v_5109_);
lean_dec(v_k_5108_);
v___x_5115_ = lean_nat_add(v___x_5105_, v_size_5106_);
v___x_5116_ = lean_nat_add(v___x_5115_, v_size_5107_);
lean_dec(v_size_5107_);
lean_dec(v___x_5115_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_impl_5104_);
lean_ctor_set(v___x_5100_, 0, v___x_5116_);
v___x_5118_ = v___x_5100_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5119_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5119_, 3, v_l_5097_);
lean_ctor_set(v_reuseFailAlloc_5119_, 4, v_impl_5104_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
else
{
lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5183_; 
v_isSharedCheck_5183_ = !lean_is_exclusive(v_impl_5104_);
if (v_isSharedCheck_5183_ == 0)
{
lean_object* v_unused_5184_; lean_object* v_unused_5185_; lean_object* v_unused_5186_; lean_object* v_unused_5187_; lean_object* v_unused_5188_; 
v_unused_5184_ = lean_ctor_get(v_impl_5104_, 4);
lean_dec(v_unused_5184_);
v_unused_5185_ = lean_ctor_get(v_impl_5104_, 3);
lean_dec(v_unused_5185_);
v_unused_5186_ = lean_ctor_get(v_impl_5104_, 2);
lean_dec(v_unused_5186_);
v_unused_5187_ = lean_ctor_get(v_impl_5104_, 1);
lean_dec(v_unused_5187_);
v_unused_5188_ = lean_ctor_get(v_impl_5104_, 0);
lean_dec(v_unused_5188_);
v___x_5121_ = v_impl_5104_;
v_isShared_5122_ = v_isSharedCheck_5183_;
goto v_resetjp_5120_;
}
else
{
lean_dec(v_impl_5104_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5183_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v_size_5123_; lean_object* v_k_5124_; lean_object* v_v_5125_; lean_object* v_l_5126_; lean_object* v_r_5127_; lean_object* v_size_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; 
v_size_5123_ = lean_ctor_get(v_l_5110_, 0);
v_k_5124_ = lean_ctor_get(v_l_5110_, 1);
v_v_5125_ = lean_ctor_get(v_l_5110_, 2);
v_l_5126_ = lean_ctor_get(v_l_5110_, 3);
v_r_5127_ = lean_ctor_get(v_l_5110_, 4);
v_size_5128_ = lean_ctor_get(v_r_5111_, 0);
v___x_5129_ = lean_unsigned_to_nat(2u);
v___x_5130_ = lean_nat_mul(v___x_5129_, v_size_5128_);
v___x_5131_ = lean_nat_dec_lt(v_size_5123_, v___x_5130_);
lean_dec(v___x_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5159_; 
lean_inc(v_r_5127_);
lean_inc(v_l_5126_);
lean_inc(v_v_5125_);
lean_inc(v_k_5124_);
v_isSharedCheck_5159_ = !lean_is_exclusive(v_l_5110_);
if (v_isSharedCheck_5159_ == 0)
{
lean_object* v_unused_5160_; lean_object* v_unused_5161_; lean_object* v_unused_5162_; lean_object* v_unused_5163_; lean_object* v_unused_5164_; 
v_unused_5160_ = lean_ctor_get(v_l_5110_, 4);
lean_dec(v_unused_5160_);
v_unused_5161_ = lean_ctor_get(v_l_5110_, 3);
lean_dec(v_unused_5161_);
v_unused_5162_ = lean_ctor_get(v_l_5110_, 2);
lean_dec(v_unused_5162_);
v_unused_5163_ = lean_ctor_get(v_l_5110_, 1);
lean_dec(v_unused_5163_);
v_unused_5164_ = lean_ctor_get(v_l_5110_, 0);
lean_dec(v_unused_5164_);
v___x_5133_ = v_l_5110_;
v_isShared_5134_ = v_isSharedCheck_5159_;
goto v_resetjp_5132_;
}
else
{
lean_dec(v_l_5110_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5159_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5149_; 
v___x_5135_ = lean_nat_add(v___x_5105_, v_size_5106_);
v___x_5136_ = lean_nat_add(v___x_5135_, v_size_5107_);
lean_dec(v_size_5107_);
if (lean_obj_tag(v_l_5126_) == 0)
{
lean_object* v_size_5157_; 
v_size_5157_ = lean_ctor_get(v_l_5126_, 0);
lean_inc(v_size_5157_);
v___y_5149_ = v_size_5157_;
goto v___jp_5148_;
}
else
{
lean_object* v___x_5158_; 
v___x_5158_ = lean_unsigned_to_nat(0u);
v___y_5149_ = v___x_5158_;
goto v___jp_5148_;
}
v___jp_5137_:
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
v___x_5141_ = lean_nat_add(v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec(v___y_5139_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 4, v_r_5111_);
lean_ctor_set(v___x_5133_, 3, v_r_5127_);
lean_ctor_set(v___x_5133_, 2, v_v_5109_);
lean_ctor_set(v___x_5133_, 1, v_k_5108_);
lean_ctor_set(v___x_5133_, 0, v___x_5141_);
v___x_5143_ = v___x_5133_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5141_);
lean_ctor_set(v_reuseFailAlloc_5147_, 1, v_k_5108_);
lean_ctor_set(v_reuseFailAlloc_5147_, 2, v_v_5109_);
lean_ctor_set(v_reuseFailAlloc_5147_, 3, v_r_5127_);
lean_ctor_set(v_reuseFailAlloc_5147_, 4, v_r_5111_);
v___x_5143_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___x_5145_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v___x_5143_);
lean_ctor_set(v___x_5121_, 3, v___y_5138_);
lean_ctor_set(v___x_5121_, 2, v_v_5125_);
lean_ctor_set(v___x_5121_, 1, v_k_5124_);
lean_ctor_set(v___x_5121_, 0, v___x_5136_);
v___x_5145_ = v___x_5121_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_k_5124_);
lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_v_5125_);
lean_ctor_set(v_reuseFailAlloc_5146_, 3, v___y_5138_);
lean_ctor_set(v_reuseFailAlloc_5146_, 4, v___x_5143_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
v___jp_5148_:
{
lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5150_ = lean_nat_add(v___x_5135_, v___y_5149_);
lean_dec(v___y_5149_);
lean_dec(v___x_5135_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_l_5126_);
lean_ctor_set(v___x_5100_, 0, v___x_5150_);
v___x_5152_ = v___x_5100_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5156_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5156_, 3, v_l_5097_);
lean_ctor_set(v_reuseFailAlloc_5156_, 4, v_l_5126_);
v___x_5152_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
lean_object* v___x_5153_; 
v___x_5153_ = lean_nat_add(v___x_5105_, v_size_5128_);
if (lean_obj_tag(v_r_5127_) == 0)
{
lean_object* v_size_5154_; 
v_size_5154_ = lean_ctor_get(v_r_5127_, 0);
lean_inc(v_size_5154_);
v___y_5138_ = v___x_5152_;
v___y_5139_ = v___x_5153_;
v___y_5140_ = v_size_5154_;
goto v___jp_5137_;
}
else
{
lean_object* v___x_5155_; 
v___x_5155_ = lean_unsigned_to_nat(0u);
v___y_5138_ = v___x_5152_;
v___y_5139_ = v___x_5153_;
v___y_5140_ = v___x_5155_;
goto v___jp_5137_;
}
}
}
}
}
else
{
lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5169_; 
lean_del_object(v___x_5100_);
v___x_5165_ = lean_nat_add(v___x_5105_, v_size_5106_);
v___x_5166_ = lean_nat_add(v___x_5165_, v_size_5107_);
lean_dec(v_size_5107_);
v___x_5167_ = lean_nat_add(v___x_5165_, v_size_5123_);
lean_dec(v___x_5165_);
lean_inc_ref(v_l_5097_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_l_5110_);
lean_ctor_set(v___x_5121_, 3, v_l_5097_);
lean_ctor_set(v___x_5121_, 2, v_v_5096_);
lean_ctor_set(v___x_5121_, 1, v_k_5095_);
lean_ctor_set(v___x_5121_, 0, v___x_5167_);
v___x_5169_ = v___x_5121_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5182_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5182_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5182_, 3, v_l_5097_);
lean_ctor_set(v_reuseFailAlloc_5182_, 4, v_l_5110_);
v___x_5169_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
v_isSharedCheck_5176_ = !lean_is_exclusive(v_l_5097_);
if (v_isSharedCheck_5176_ == 0)
{
lean_object* v_unused_5177_; lean_object* v_unused_5178_; lean_object* v_unused_5179_; lean_object* v_unused_5180_; lean_object* v_unused_5181_; 
v_unused_5177_ = lean_ctor_get(v_l_5097_, 4);
lean_dec(v_unused_5177_);
v_unused_5178_ = lean_ctor_get(v_l_5097_, 3);
lean_dec(v_unused_5178_);
v_unused_5179_ = lean_ctor_get(v_l_5097_, 2);
lean_dec(v_unused_5179_);
v_unused_5180_ = lean_ctor_get(v_l_5097_, 1);
lean_dec(v_unused_5180_);
v_unused_5181_ = lean_ctor_get(v_l_5097_, 0);
lean_dec(v_unused_5181_);
v___x_5171_ = v_l_5097_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_dec(v_l_5097_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 4, v_r_5111_);
lean_ctor_set(v___x_5171_, 3, v___x_5169_);
lean_ctor_set(v___x_5171_, 2, v_v_5109_);
lean_ctor_set(v___x_5171_, 1, v_k_5108_);
lean_ctor_set(v___x_5171_, 0, v___x_5166_);
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5166_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_k_5108_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_v_5109_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v___x_5169_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v_r_5111_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5189_; 
v_l_5189_ = lean_ctor_get(v_impl_5104_, 3);
lean_inc(v_l_5189_);
if (lean_obj_tag(v_l_5189_) == 0)
{
lean_object* v_r_5190_; lean_object* v_k_5191_; lean_object* v_v_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5215_; 
v_r_5190_ = lean_ctor_get(v_impl_5104_, 4);
v_k_5191_ = lean_ctor_get(v_impl_5104_, 1);
v_v_5192_ = lean_ctor_get(v_impl_5104_, 2);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_impl_5104_);
if (v_isSharedCheck_5215_ == 0)
{
lean_object* v_unused_5216_; lean_object* v_unused_5217_; 
v_unused_5216_ = lean_ctor_get(v_impl_5104_, 3);
lean_dec(v_unused_5216_);
v_unused_5217_ = lean_ctor_get(v_impl_5104_, 0);
lean_dec(v_unused_5217_);
v___x_5194_ = v_impl_5104_;
v_isShared_5195_ = v_isSharedCheck_5215_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_r_5190_);
lean_inc(v_v_5192_);
lean_inc(v_k_5191_);
lean_dec(v_impl_5104_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5215_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v_k_5196_; lean_object* v_v_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5211_; 
v_k_5196_ = lean_ctor_get(v_l_5189_, 1);
v_v_5197_ = lean_ctor_get(v_l_5189_, 2);
v_isSharedCheck_5211_ = !lean_is_exclusive(v_l_5189_);
if (v_isSharedCheck_5211_ == 0)
{
lean_object* v_unused_5212_; lean_object* v_unused_5213_; lean_object* v_unused_5214_; 
v_unused_5212_ = lean_ctor_get(v_l_5189_, 4);
lean_dec(v_unused_5212_);
v_unused_5213_ = lean_ctor_get(v_l_5189_, 3);
lean_dec(v_unused_5213_);
v_unused_5214_ = lean_ctor_get(v_l_5189_, 0);
lean_dec(v_unused_5214_);
v___x_5199_ = v_l_5189_;
v_isShared_5200_ = v_isSharedCheck_5211_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_v_5197_);
lean_inc(v_k_5196_);
lean_dec(v_l_5189_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5211_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5201_; lean_object* v___x_5203_; 
v___x_5201_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5190_, 2);
if (v_isShared_5200_ == 0)
{
lean_ctor_set(v___x_5199_, 4, v_r_5190_);
lean_ctor_set(v___x_5199_, 3, v_r_5190_);
lean_ctor_set(v___x_5199_, 2, v_v_5096_);
lean_ctor_set(v___x_5199_, 1, v_k_5095_);
lean_ctor_set(v___x_5199_, 0, v___x_5105_);
v___x_5203_ = v___x_5199_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5210_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5210_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5210_, 3, v_r_5190_);
lean_ctor_set(v_reuseFailAlloc_5210_, 4, v_r_5190_);
v___x_5203_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5205_; 
lean_inc(v_r_5190_);
if (v_isShared_5195_ == 0)
{
lean_ctor_set(v___x_5194_, 3, v_r_5190_);
lean_ctor_set(v___x_5194_, 0, v___x_5105_);
v___x_5205_ = v___x_5194_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_k_5191_);
lean_ctor_set(v_reuseFailAlloc_5209_, 2, v_v_5192_);
lean_ctor_set(v_reuseFailAlloc_5209_, 3, v_r_5190_);
lean_ctor_set(v_reuseFailAlloc_5209_, 4, v_r_5190_);
v___x_5205_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
lean_object* v___x_5207_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v___x_5205_);
lean_ctor_set(v___x_5100_, 3, v___x_5203_);
lean_ctor_set(v___x_5100_, 2, v_v_5197_);
lean_ctor_set(v___x_5100_, 1, v_k_5196_);
lean_ctor_set(v___x_5100_, 0, v___x_5201_);
v___x_5207_ = v___x_5100_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5201_);
lean_ctor_set(v_reuseFailAlloc_5208_, 1, v_k_5196_);
lean_ctor_set(v_reuseFailAlloc_5208_, 2, v_v_5197_);
lean_ctor_set(v_reuseFailAlloc_5208_, 3, v___x_5203_);
lean_ctor_set(v_reuseFailAlloc_5208_, 4, v___x_5205_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
}
}
else
{
lean_object* v_r_5218_; 
v_r_5218_ = lean_ctor_get(v_impl_5104_, 4);
lean_inc(v_r_5218_);
if (lean_obj_tag(v_r_5218_) == 0)
{
lean_object* v_k_5219_; lean_object* v_v_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5231_; 
v_k_5219_ = lean_ctor_get(v_impl_5104_, 1);
v_v_5220_ = lean_ctor_get(v_impl_5104_, 2);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_impl_5104_);
if (v_isSharedCheck_5231_ == 0)
{
lean_object* v_unused_5232_; lean_object* v_unused_5233_; lean_object* v_unused_5234_; 
v_unused_5232_ = lean_ctor_get(v_impl_5104_, 4);
lean_dec(v_unused_5232_);
v_unused_5233_ = lean_ctor_get(v_impl_5104_, 3);
lean_dec(v_unused_5233_);
v_unused_5234_ = lean_ctor_get(v_impl_5104_, 0);
lean_dec(v_unused_5234_);
v___x_5222_ = v_impl_5104_;
v_isShared_5223_ = v_isSharedCheck_5231_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_v_5220_);
lean_inc(v_k_5219_);
lean_dec(v_impl_5104_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5231_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5224_; lean_object* v___x_5226_; 
v___x_5224_ = lean_unsigned_to_nat(3u);
if (v_isShared_5223_ == 0)
{
lean_ctor_set(v___x_5222_, 4, v_l_5189_);
lean_ctor_set(v___x_5222_, 2, v_v_5096_);
lean_ctor_set(v___x_5222_, 1, v_k_5095_);
lean_ctor_set(v___x_5222_, 0, v___x_5105_);
v___x_5226_ = v___x_5222_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5230_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5230_, 3, v_l_5189_);
lean_ctor_set(v_reuseFailAlloc_5230_, 4, v_l_5189_);
v___x_5226_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5228_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_r_5218_);
lean_ctor_set(v___x_5100_, 3, v___x_5226_);
lean_ctor_set(v___x_5100_, 2, v_v_5220_);
lean_ctor_set(v___x_5100_, 1, v_k_5219_);
lean_ctor_set(v___x_5100_, 0, v___x_5224_);
v___x_5228_ = v___x_5100_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5229_, 1, v_k_5219_);
lean_ctor_set(v_reuseFailAlloc_5229_, 2, v_v_5220_);
lean_ctor_set(v_reuseFailAlloc_5229_, 3, v___x_5226_);
lean_ctor_set(v_reuseFailAlloc_5229_, 4, v_r_5218_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v___x_5235_; lean_object* v___x_5237_; 
v___x_5235_ = lean_unsigned_to_nat(2u);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_impl_5104_);
lean_ctor_set(v___x_5100_, 3, v_r_5218_);
lean_ctor_set(v___x_5100_, 0, v___x_5235_);
v___x_5237_ = v___x_5100_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5235_);
lean_ctor_set(v_reuseFailAlloc_5238_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5238_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5238_, 3, v_r_5218_);
lean_ctor_set(v_reuseFailAlloc_5238_, 4, v_impl_5104_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
}
}
else
{
lean_object* v___x_5240_; 
lean_dec(v_v_5096_);
lean_dec(v_k_5095_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 2, v_v_5092_);
lean_ctor_set(v___x_5100_, 1, v_k_5091_);
v___x_5240_ = v___x_5100_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_size_5094_);
lean_ctor_set(v_reuseFailAlloc_5241_, 1, v_k_5091_);
lean_ctor_set(v_reuseFailAlloc_5241_, 2, v_v_5092_);
lean_ctor_set(v_reuseFailAlloc_5241_, 3, v_l_5097_);
lean_ctor_set(v_reuseFailAlloc_5241_, 4, v_r_5098_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
else
{
lean_object* v_impl_5242_; lean_object* v___x_5243_; 
lean_dec(v_size_5094_);
v_impl_5242_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5091_, v_v_5092_, v_l_5097_);
v___x_5243_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5098_) == 0)
{
lean_object* v_size_5244_; lean_object* v_size_5245_; lean_object* v_k_5246_; lean_object* v_v_5247_; lean_object* v_l_5248_; lean_object* v_r_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; uint8_t v___x_5252_; 
v_size_5244_ = lean_ctor_get(v_r_5098_, 0);
v_size_5245_ = lean_ctor_get(v_impl_5242_, 0);
lean_inc(v_size_5245_);
v_k_5246_ = lean_ctor_get(v_impl_5242_, 1);
lean_inc(v_k_5246_);
v_v_5247_ = lean_ctor_get(v_impl_5242_, 2);
lean_inc(v_v_5247_);
v_l_5248_ = lean_ctor_get(v_impl_5242_, 3);
lean_inc(v_l_5248_);
v_r_5249_ = lean_ctor_get(v_impl_5242_, 4);
lean_inc(v_r_5249_);
v___x_5250_ = lean_unsigned_to_nat(3u);
v___x_5251_ = lean_nat_mul(v___x_5250_, v_size_5244_);
v___x_5252_ = lean_nat_dec_lt(v___x_5251_, v_size_5245_);
lean_dec(v___x_5251_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5256_; 
lean_dec(v_r_5249_);
lean_dec(v_l_5248_);
lean_dec(v_v_5247_);
lean_dec(v_k_5246_);
v___x_5253_ = lean_nat_add(v___x_5243_, v_size_5245_);
lean_dec(v_size_5245_);
v___x_5254_ = lean_nat_add(v___x_5253_, v_size_5244_);
lean_dec(v___x_5253_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 3, v_impl_5242_);
lean_ctor_set(v___x_5100_, 0, v___x_5254_);
v___x_5256_ = v___x_5100_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5254_);
lean_ctor_set(v_reuseFailAlloc_5257_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5257_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5257_, 3, v_impl_5242_);
lean_ctor_set(v_reuseFailAlloc_5257_, 4, v_r_5098_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
else
{
lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5323_; 
v_isSharedCheck_5323_ = !lean_is_exclusive(v_impl_5242_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; lean_object* v_unused_5325_; lean_object* v_unused_5326_; lean_object* v_unused_5327_; lean_object* v_unused_5328_; 
v_unused_5324_ = lean_ctor_get(v_impl_5242_, 4);
lean_dec(v_unused_5324_);
v_unused_5325_ = lean_ctor_get(v_impl_5242_, 3);
lean_dec(v_unused_5325_);
v_unused_5326_ = lean_ctor_get(v_impl_5242_, 2);
lean_dec(v_unused_5326_);
v_unused_5327_ = lean_ctor_get(v_impl_5242_, 1);
lean_dec(v_unused_5327_);
v_unused_5328_ = lean_ctor_get(v_impl_5242_, 0);
lean_dec(v_unused_5328_);
v___x_5259_ = v_impl_5242_;
v_isShared_5260_ = v_isSharedCheck_5323_;
goto v_resetjp_5258_;
}
else
{
lean_dec(v_impl_5242_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5323_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v_size_5261_; lean_object* v_size_5262_; lean_object* v_k_5263_; lean_object* v_v_5264_; lean_object* v_l_5265_; lean_object* v_r_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; uint8_t v___x_5269_; 
v_size_5261_ = lean_ctor_get(v_l_5248_, 0);
v_size_5262_ = lean_ctor_get(v_r_5249_, 0);
v_k_5263_ = lean_ctor_get(v_r_5249_, 1);
v_v_5264_ = lean_ctor_get(v_r_5249_, 2);
v_l_5265_ = lean_ctor_get(v_r_5249_, 3);
v_r_5266_ = lean_ctor_get(v_r_5249_, 4);
v___x_5267_ = lean_unsigned_to_nat(2u);
v___x_5268_ = lean_nat_mul(v___x_5267_, v_size_5261_);
v___x_5269_ = lean_nat_dec_lt(v_size_5262_, v___x_5268_);
lean_dec(v___x_5268_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5298_; 
lean_inc(v_r_5266_);
lean_inc(v_l_5265_);
lean_inc(v_v_5264_);
lean_inc(v_k_5263_);
v_isSharedCheck_5298_ = !lean_is_exclusive(v_r_5249_);
if (v_isSharedCheck_5298_ == 0)
{
lean_object* v_unused_5299_; lean_object* v_unused_5300_; lean_object* v_unused_5301_; lean_object* v_unused_5302_; lean_object* v_unused_5303_; 
v_unused_5299_ = lean_ctor_get(v_r_5249_, 4);
lean_dec(v_unused_5299_);
v_unused_5300_ = lean_ctor_get(v_r_5249_, 3);
lean_dec(v_unused_5300_);
v_unused_5301_ = lean_ctor_get(v_r_5249_, 2);
lean_dec(v_unused_5301_);
v_unused_5302_ = lean_ctor_get(v_r_5249_, 1);
lean_dec(v_unused_5302_);
v_unused_5303_ = lean_ctor_get(v_r_5249_, 0);
lean_dec(v_unused_5303_);
v___x_5271_ = v_r_5249_;
v_isShared_5272_ = v_isSharedCheck_5298_;
goto v_resetjp_5270_;
}
else
{
lean_dec(v_r_5249_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5298_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___y_5276_; lean_object* v___y_5277_; lean_object* v___y_5278_; lean_object* v___x_5286_; lean_object* v___y_5288_; 
v___x_5273_ = lean_nat_add(v___x_5243_, v_size_5245_);
lean_dec(v_size_5245_);
v___x_5274_ = lean_nat_add(v___x_5273_, v_size_5244_);
lean_dec(v___x_5273_);
v___x_5286_ = lean_nat_add(v___x_5243_, v_size_5261_);
if (lean_obj_tag(v_l_5265_) == 0)
{
lean_object* v_size_5296_; 
v_size_5296_ = lean_ctor_get(v_l_5265_, 0);
lean_inc(v_size_5296_);
v___y_5288_ = v_size_5296_;
goto v___jp_5287_;
}
else
{
lean_object* v___x_5297_; 
v___x_5297_ = lean_unsigned_to_nat(0u);
v___y_5288_ = v___x_5297_;
goto v___jp_5287_;
}
v___jp_5275_:
{
lean_object* v___x_5279_; lean_object* v___x_5281_; 
v___x_5279_ = lean_nat_add(v___y_5277_, v___y_5278_);
lean_dec(v___y_5278_);
lean_dec(v___y_5277_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 4, v_r_5098_);
lean_ctor_set(v___x_5271_, 3, v_r_5266_);
lean_ctor_set(v___x_5271_, 2, v_v_5096_);
lean_ctor_set(v___x_5271_, 1, v_k_5095_);
lean_ctor_set(v___x_5271_, 0, v___x_5279_);
v___x_5281_ = v___x_5271_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5285_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5285_, 3, v_r_5266_);
lean_ctor_set(v_reuseFailAlloc_5285_, 4, v_r_5098_);
v___x_5281_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
lean_object* v___x_5283_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 4, v___x_5281_);
lean_ctor_set(v___x_5259_, 3, v___y_5276_);
lean_ctor_set(v___x_5259_, 2, v_v_5264_);
lean_ctor_set(v___x_5259_, 1, v_k_5263_);
lean_ctor_set(v___x_5259_, 0, v___x_5274_);
v___x_5283_ = v___x_5259_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5274_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v_k_5263_);
lean_ctor_set(v_reuseFailAlloc_5284_, 2, v_v_5264_);
lean_ctor_set(v_reuseFailAlloc_5284_, 3, v___y_5276_);
lean_ctor_set(v_reuseFailAlloc_5284_, 4, v___x_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
v___jp_5287_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = lean_nat_add(v___x_5286_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec(v___x_5286_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_l_5265_);
lean_ctor_set(v___x_5100_, 3, v_l_5248_);
lean_ctor_set(v___x_5100_, 2, v_v_5247_);
lean_ctor_set(v___x_5100_, 1, v_k_5246_);
lean_ctor_set(v___x_5100_, 0, v___x_5289_);
v___x_5291_ = v___x_5100_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5289_);
lean_ctor_set(v_reuseFailAlloc_5295_, 1, v_k_5246_);
lean_ctor_set(v_reuseFailAlloc_5295_, 2, v_v_5247_);
lean_ctor_set(v_reuseFailAlloc_5295_, 3, v_l_5248_);
lean_ctor_set(v_reuseFailAlloc_5295_, 4, v_l_5265_);
v___x_5291_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
lean_object* v___x_5292_; 
v___x_5292_ = lean_nat_add(v___x_5243_, v_size_5244_);
if (lean_obj_tag(v_r_5266_) == 0)
{
lean_object* v_size_5293_; 
v_size_5293_ = lean_ctor_get(v_r_5266_, 0);
lean_inc(v_size_5293_);
v___y_5276_ = v___x_5291_;
v___y_5277_ = v___x_5292_;
v___y_5278_ = v_size_5293_;
goto v___jp_5275_;
}
else
{
lean_object* v___x_5294_; 
v___x_5294_ = lean_unsigned_to_nat(0u);
v___y_5276_ = v___x_5291_;
v___y_5277_ = v___x_5292_;
v___y_5278_ = v___x_5294_;
goto v___jp_5275_;
}
}
}
}
}
else
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5309_; 
lean_del_object(v___x_5100_);
v___x_5304_ = lean_nat_add(v___x_5243_, v_size_5245_);
lean_dec(v_size_5245_);
v___x_5305_ = lean_nat_add(v___x_5304_, v_size_5244_);
lean_dec(v___x_5304_);
v___x_5306_ = lean_nat_add(v___x_5243_, v_size_5244_);
v___x_5307_ = lean_nat_add(v___x_5306_, v_size_5262_);
lean_dec(v___x_5306_);
lean_inc_ref(v_r_5098_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 4, v_r_5098_);
lean_ctor_set(v___x_5259_, 3, v_r_5249_);
lean_ctor_set(v___x_5259_, 2, v_v_5096_);
lean_ctor_set(v___x_5259_, 1, v_k_5095_);
lean_ctor_set(v___x_5259_, 0, v___x_5307_);
v___x_5309_ = v___x_5259_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5322_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5322_, 3, v_r_5249_);
lean_ctor_set(v_reuseFailAlloc_5322_, 4, v_r_5098_);
v___x_5309_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5316_; 
v_isSharedCheck_5316_ = !lean_is_exclusive(v_r_5098_);
if (v_isSharedCheck_5316_ == 0)
{
lean_object* v_unused_5317_; lean_object* v_unused_5318_; lean_object* v_unused_5319_; lean_object* v_unused_5320_; lean_object* v_unused_5321_; 
v_unused_5317_ = lean_ctor_get(v_r_5098_, 4);
lean_dec(v_unused_5317_);
v_unused_5318_ = lean_ctor_get(v_r_5098_, 3);
lean_dec(v_unused_5318_);
v_unused_5319_ = lean_ctor_get(v_r_5098_, 2);
lean_dec(v_unused_5319_);
v_unused_5320_ = lean_ctor_get(v_r_5098_, 1);
lean_dec(v_unused_5320_);
v_unused_5321_ = lean_ctor_get(v_r_5098_, 0);
lean_dec(v_unused_5321_);
v___x_5311_ = v_r_5098_;
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
else
{
lean_dec(v_r_5098_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5314_; 
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 4, v___x_5309_);
lean_ctor_set(v___x_5311_, 3, v_l_5248_);
lean_ctor_set(v___x_5311_, 2, v_v_5247_);
lean_ctor_set(v___x_5311_, 1, v_k_5246_);
lean_ctor_set(v___x_5311_, 0, v___x_5305_);
v___x_5314_ = v___x_5311_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5305_);
lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_k_5246_);
lean_ctor_set(v_reuseFailAlloc_5315_, 2, v_v_5247_);
lean_ctor_set(v_reuseFailAlloc_5315_, 3, v_l_5248_);
lean_ctor_set(v_reuseFailAlloc_5315_, 4, v___x_5309_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5329_; 
v_l_5329_ = lean_ctor_get(v_impl_5242_, 3);
lean_inc(v_l_5329_);
if (lean_obj_tag(v_l_5329_) == 0)
{
lean_object* v_r_5330_; lean_object* v_k_5331_; lean_object* v_v_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5343_; 
v_r_5330_ = lean_ctor_get(v_impl_5242_, 4);
v_k_5331_ = lean_ctor_get(v_impl_5242_, 1);
v_v_5332_ = lean_ctor_get(v_impl_5242_, 2);
v_isSharedCheck_5343_ = !lean_is_exclusive(v_impl_5242_);
if (v_isSharedCheck_5343_ == 0)
{
lean_object* v_unused_5344_; lean_object* v_unused_5345_; 
v_unused_5344_ = lean_ctor_get(v_impl_5242_, 3);
lean_dec(v_unused_5344_);
v_unused_5345_ = lean_ctor_get(v_impl_5242_, 0);
lean_dec(v_unused_5345_);
v___x_5334_ = v_impl_5242_;
v_isShared_5335_ = v_isSharedCheck_5343_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_r_5330_);
lean_inc(v_v_5332_);
lean_inc(v_k_5331_);
lean_dec(v_impl_5242_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5343_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5336_; lean_object* v___x_5338_; 
v___x_5336_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5330_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 3, v_r_5330_);
lean_ctor_set(v___x_5334_, 2, v_v_5096_);
lean_ctor_set(v___x_5334_, 1, v_k_5095_);
lean_ctor_set(v___x_5334_, 0, v___x_5243_);
v___x_5338_ = v___x_5334_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5342_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5342_, 3, v_r_5330_);
lean_ctor_set(v_reuseFailAlloc_5342_, 4, v_r_5330_);
v___x_5338_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5340_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v___x_5338_);
lean_ctor_set(v___x_5100_, 3, v_l_5329_);
lean_ctor_set(v___x_5100_, 2, v_v_5332_);
lean_ctor_set(v___x_5100_, 1, v_k_5331_);
lean_ctor_set(v___x_5100_, 0, v___x_5336_);
v___x_5340_ = v___x_5100_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5341_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5341_, 3, v_l_5329_);
lean_ctor_set(v_reuseFailAlloc_5341_, 4, v___x_5338_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
else
{
lean_object* v_r_5346_; 
v_r_5346_ = lean_ctor_get(v_impl_5242_, 4);
lean_inc(v_r_5346_);
if (lean_obj_tag(v_r_5346_) == 0)
{
lean_object* v_k_5347_; lean_object* v_v_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5371_; 
v_k_5347_ = lean_ctor_get(v_impl_5242_, 1);
v_v_5348_ = lean_ctor_get(v_impl_5242_, 2);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_impl_5242_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; lean_object* v_unused_5373_; lean_object* v_unused_5374_; 
v_unused_5372_ = lean_ctor_get(v_impl_5242_, 4);
lean_dec(v_unused_5372_);
v_unused_5373_ = lean_ctor_get(v_impl_5242_, 3);
lean_dec(v_unused_5373_);
v_unused_5374_ = lean_ctor_get(v_impl_5242_, 0);
lean_dec(v_unused_5374_);
v___x_5350_ = v_impl_5242_;
v_isShared_5351_ = v_isSharedCheck_5371_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_v_5348_);
lean_inc(v_k_5347_);
lean_dec(v_impl_5242_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5371_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v_k_5352_; lean_object* v_v_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5367_; 
v_k_5352_ = lean_ctor_get(v_r_5346_, 1);
v_v_5353_ = lean_ctor_get(v_r_5346_, 2);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_r_5346_);
if (v_isSharedCheck_5367_ == 0)
{
lean_object* v_unused_5368_; lean_object* v_unused_5369_; lean_object* v_unused_5370_; 
v_unused_5368_ = lean_ctor_get(v_r_5346_, 4);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_r_5346_, 3);
lean_dec(v_unused_5369_);
v_unused_5370_ = lean_ctor_get(v_r_5346_, 0);
lean_dec(v_unused_5370_);
v___x_5355_ = v_r_5346_;
v_isShared_5356_ = v_isSharedCheck_5367_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_v_5353_);
lean_inc(v_k_5352_);
lean_dec(v_r_5346_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5367_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v___x_5359_; 
v___x_5357_ = lean_unsigned_to_nat(3u);
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 4, v_l_5329_);
lean_ctor_set(v___x_5355_, 3, v_l_5329_);
lean_ctor_set(v___x_5355_, 2, v_v_5348_);
lean_ctor_set(v___x_5355_, 1, v_k_5347_);
lean_ctor_set(v___x_5355_, 0, v___x_5243_);
v___x_5359_ = v___x_5355_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_k_5347_);
lean_ctor_set(v_reuseFailAlloc_5366_, 2, v_v_5348_);
lean_ctor_set(v_reuseFailAlloc_5366_, 3, v_l_5329_);
lean_ctor_set(v_reuseFailAlloc_5366_, 4, v_l_5329_);
v___x_5359_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
lean_object* v___x_5361_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_l_5329_);
lean_ctor_set(v___x_5350_, 2, v_v_5096_);
lean_ctor_set(v___x_5350_, 1, v_k_5095_);
lean_ctor_set(v___x_5350_, 0, v___x_5243_);
v___x_5361_ = v___x_5350_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5365_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5365_, 3, v_l_5329_);
lean_ctor_set(v_reuseFailAlloc_5365_, 4, v_l_5329_);
v___x_5361_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5363_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v___x_5361_);
lean_ctor_set(v___x_5100_, 3, v___x_5359_);
lean_ctor_set(v___x_5100_, 2, v_v_5353_);
lean_ctor_set(v___x_5100_, 1, v_k_5352_);
lean_ctor_set(v___x_5100_, 0, v___x_5357_);
v___x_5363_ = v___x_5100_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_k_5352_);
lean_ctor_set(v_reuseFailAlloc_5364_, 2, v_v_5353_);
lean_ctor_set(v_reuseFailAlloc_5364_, 3, v___x_5359_);
lean_ctor_set(v_reuseFailAlloc_5364_, 4, v___x_5361_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
v___x_5375_ = lean_unsigned_to_nat(2u);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 4, v_r_5346_);
lean_ctor_set(v___x_5100_, 3, v_impl_5242_);
lean_ctor_set(v___x_5100_, 0, v___x_5375_);
v___x_5377_ = v___x_5100_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5378_, 1, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5378_, 2, v_v_5096_);
lean_ctor_set(v_reuseFailAlloc_5378_, 3, v_impl_5242_);
lean_ctor_set(v_reuseFailAlloc_5378_, 4, v_r_5346_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5380_ = lean_unsigned_to_nat(1u);
v___x_5381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5380_);
lean_ctor_set(v___x_5381_, 1, v_k_5091_);
lean_ctor_set(v___x_5381_, 2, v_v_5092_);
lean_ctor_set(v___x_5381_, 3, v_t_5093_);
lean_ctor_set(v___x_5381_, 4, v_t_5093_);
return v___x_5381_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5382_, lean_object* v_t_5383_){
_start:
{
if (lean_obj_tag(v_t_5383_) == 0)
{
lean_object* v_k_5384_; lean_object* v_l_5385_; lean_object* v_r_5386_; uint8_t v___x_5387_; 
v_k_5384_ = lean_ctor_get(v_t_5383_, 1);
v_l_5385_ = lean_ctor_get(v_t_5383_, 3);
v_r_5386_ = lean_ctor_get(v_t_5383_, 4);
v___x_5387_ = lean_nat_dec_lt(v_k_5384_, v_k_5382_);
if (v___x_5387_ == 0)
{
uint8_t v___x_5388_; 
v___x_5388_ = lean_nat_dec_eq(v_k_5384_, v_k_5382_);
if (v___x_5388_ == 0)
{
v_t_5383_ = v_r_5386_;
goto _start;
}
else
{
return v___x_5388_;
}
}
else
{
v_t_5383_ = v_l_5385_;
goto _start;
}
}
else
{
uint8_t v___x_5391_; 
v___x_5391_ = 0;
return v___x_5391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5392_, lean_object* v_t_5393_){
_start:
{
uint8_t v_res_5394_; lean_object* v_r_5395_; 
v_res_5394_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5392_, v_t_5393_);
lean_dec(v_t_5393_);
lean_dec(v_k_5392_);
v_r_5395_ = lean_box(v_res_5394_);
return v_r_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5396_, lean_object* v_e_5397_){
_start:
{
lean_object* v_defaultInstances_5398_; lean_object* v_priorities_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5426_; 
v_defaultInstances_5398_ = lean_ctor_get(v_d_5396_, 0);
v_priorities_5399_ = lean_ctor_get(v_d_5396_, 1);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_d_5396_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5401_ = v_d_5396_;
v_isShared_5402_ = v_isSharedCheck_5426_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_priorities_5399_);
lean_inc(v_defaultInstances_5398_);
lean_dec(v_d_5396_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5426_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v_className_5403_; lean_object* v_instanceName_5404_; lean_object* v_priority_5405_; lean_object* v___y_5407_; uint8_t v___x_5423_; 
v_className_5403_ = lean_ctor_get(v_e_5397_, 0);
lean_inc(v_className_5403_);
v_instanceName_5404_ = lean_ctor_get(v_e_5397_, 1);
lean_inc(v_instanceName_5404_);
v_priority_5405_ = lean_ctor_get(v_e_5397_, 2);
lean_inc(v_priority_5405_);
lean_dec_ref(v_e_5397_);
v___x_5423_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5405_, v_priorities_5399_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = lean_box(0);
lean_inc(v_priority_5405_);
v___x_5425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5405_, v___x_5424_, v_priorities_5399_);
v___y_5407_ = v___x_5425_;
goto v___jp_5406_;
}
else
{
v___y_5407_ = v_priorities_5399_;
goto v___jp_5406_;
}
v___jp_5406_:
{
lean_object* v___x_5408_; 
v___x_5408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5398_, v_className_5403_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5409_, 0, v_instanceName_5404_);
lean_ctor_set(v___x_5409_, 1, v_priority_5405_);
v___x_5410_ = lean_box(0);
v___x_5411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5403_, v___x_5411_, v_defaultInstances_5398_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 1, v___y_5407_);
lean_ctor_set(v___x_5401_, 0, v___x_5412_);
v___x_5414_ = v___x_5401_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5412_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v___y_5407_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
else
{
lean_object* v_val_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v_val_5416_ = lean_ctor_get(v___x_5408_, 0);
lean_inc(v_val_5416_);
lean_dec_ref(v___x_5408_);
v___x_5417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5417_, 0, v_instanceName_5404_);
lean_ctor_set(v___x_5417_, 1, v_priority_5405_);
v___x_5418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___x_5417_);
lean_ctor_set(v___x_5418_, 1, v_val_5416_);
v___x_5419_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5403_, v___x_5418_, v_defaultInstances_5398_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 1, v___y_5407_);
lean_ctor_set(v___x_5401_, 0, v___x_5419_);
v___x_5421_ = v___x_5401_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5422_, 1, v___y_5407_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5427_, lean_object* v_k_5428_, lean_object* v_t_5429_){
_start:
{
uint8_t v___x_5430_; 
v___x_5430_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5428_, v_t_5429_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5431_, lean_object* v_k_5432_, lean_object* v_t_5433_){
_start:
{
uint8_t v_res_5434_; lean_object* v_r_5435_; 
v_res_5434_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5431_, v_k_5432_, v_t_5433_);
lean_dec(v_t_5433_);
lean_dec(v_k_5432_);
v_r_5435_ = lean_box(v_res_5434_);
return v_r_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5436_, lean_object* v_k_5437_, lean_object* v_v_5438_, lean_object* v_t_5439_, lean_object* v_hl_5440_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5437_, v_v_5438_, v_t_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5442_, lean_object* v_as_5443_, size_t v_i_5444_, size_t v_stop_5445_, lean_object* v_b_5446_){
_start:
{
lean_object* v___y_5448_; uint8_t v___x_5452_; 
v___x_5452_ = lean_usize_dec_eq(v_i_5444_, v_stop_5445_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; lean_object* v_instanceName_5454_; uint8_t v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5453_ = lean_array_uget_borrowed(v_as_5443_, v_i_5444_);
v_instanceName_5454_ = lean_ctor_get(v___x_5453_, 1);
v___x_5455_ = 1;
lean_inc_ref(v_env_5442_);
v___x_5456_ = l_Lean_Environment_setExporting(v_env_5442_, v___x_5455_);
lean_inc(v_instanceName_5454_);
v___x_5457_ = l_Lean_Environment_contains(v___x_5456_, v_instanceName_5454_, v___x_5452_);
if (v___x_5457_ == 0)
{
v___y_5448_ = v_b_5446_;
goto v___jp_5447_;
}
else
{
lean_object* v___x_5458_; 
lean_inc(v___x_5453_);
v___x_5458_ = lean_array_push(v_b_5446_, v___x_5453_);
v___y_5448_ = v___x_5458_;
goto v___jp_5447_;
}
}
else
{
lean_dec_ref(v_env_5442_);
return v_b_5446_;
}
v___jp_5447_:
{
size_t v___x_5449_; size_t v___x_5450_; 
v___x_5449_ = ((size_t)1ULL);
v___x_5450_ = lean_usize_add(v_i_5444_, v___x_5449_);
v_i_5444_ = v___x_5450_;
v_b_5446_ = v___y_5448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5459_, lean_object* v_as_5460_, lean_object* v_i_5461_, lean_object* v_stop_5462_, lean_object* v_b_5463_){
_start:
{
size_t v_i_boxed_5464_; size_t v_stop_boxed_5465_; lean_object* v_res_5466_; 
v_i_boxed_5464_ = lean_unbox_usize(v_i_5461_);
lean_dec(v_i_5461_);
v_stop_boxed_5465_ = lean_unbox_usize(v_stop_5462_);
lean_dec(v_stop_5462_);
v_res_5466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5459_, v_as_5460_, v_i_boxed_5464_, v_stop_boxed_5465_, v_b_5463_);
lean_dec_ref(v_as_5460_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5469_, lean_object* v_x_5470_, lean_object* v_entries_5471_){
_start:
{
lean_object* v_all_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; 
v_all_5472_ = lean_array_mk(v_entries_5471_);
v___x_5473_ = lean_unsigned_to_nat(0u);
v___x_5474_ = lean_array_get_size(v_all_5472_);
v___x_5475_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5476_ = lean_nat_dec_lt(v___x_5473_, v___x_5474_);
if (v___x_5476_ == 0)
{
lean_object* v___x_5477_; 
lean_dec_ref(v_env_5469_);
v___x_5477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5475_);
lean_ctor_set(v___x_5477_, 1, v___x_5475_);
lean_ctor_set(v___x_5477_, 2, v_all_5472_);
return v___x_5477_;
}
else
{
uint8_t v___x_5478_; 
v___x_5478_ = lean_nat_dec_le(v___x_5474_, v___x_5474_);
if (v___x_5478_ == 0)
{
if (v___x_5476_ == 0)
{
lean_object* v___x_5479_; 
lean_dec_ref(v_env_5469_);
v___x_5479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5475_);
lean_ctor_set(v___x_5479_, 1, v___x_5475_);
lean_ctor_set(v___x_5479_, 2, v_all_5472_);
return v___x_5479_;
}
else
{
size_t v___x_5480_; size_t v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5480_ = ((size_t)0ULL);
v___x_5481_ = lean_usize_of_nat(v___x_5474_);
v___x_5482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5469_, v_all_5472_, v___x_5480_, v___x_5481_, v___x_5475_);
lean_inc_ref(v___x_5482_);
v___x_5483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5482_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
lean_ctor_set(v___x_5483_, 2, v_all_5472_);
return v___x_5483_;
}
}
else
{
size_t v___x_5484_; size_t v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5484_ = ((size_t)0ULL);
v___x_5485_ = lean_usize_of_nat(v___x_5474_);
v___x_5486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5469_, v_all_5472_, v___x_5484_, v___x_5485_, v___x_5475_);
lean_inc_ref(v___x_5486_);
v___x_5487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5486_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
lean_ctor_set(v___x_5487_, 2, v_all_5472_);
return v___x_5487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5488_, lean_object* v_x_5489_, lean_object* v_entries_5490_){
_start:
{
lean_object* v_res_5491_; 
v_res_5491_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5488_, v_x_5489_, v_entries_5490_);
lean_dec_ref(v_x_5489_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5492_){
_start:
{
lean_object* v___x_5493_; 
v___x_5493_ = lean_array_mk(v_es_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5494_, size_t v_i_5495_, size_t v_stop_5496_, lean_object* v_b_5497_){
_start:
{
uint8_t v___x_5498_; 
v___x_5498_ = lean_usize_dec_eq(v_i_5495_, v_stop_5496_);
if (v___x_5498_ == 0)
{
lean_object* v___x_5499_; lean_object* v___x_5500_; size_t v___x_5501_; size_t v___x_5502_; 
v___x_5499_ = lean_array_uget_borrowed(v_as_5494_, v_i_5495_);
lean_inc(v___x_5499_);
v___x_5500_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5497_, v___x_5499_);
v___x_5501_ = ((size_t)1ULL);
v___x_5502_ = lean_usize_add(v_i_5495_, v___x_5501_);
v_i_5495_ = v___x_5502_;
v_b_5497_ = v___x_5500_;
goto _start;
}
else
{
return v_b_5497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5504_, lean_object* v_i_5505_, lean_object* v_stop_5506_, lean_object* v_b_5507_){
_start:
{
size_t v_i_boxed_5508_; size_t v_stop_boxed_5509_; lean_object* v_res_5510_; 
v_i_boxed_5508_ = lean_unbox_usize(v_i_5505_);
lean_dec(v_i_5505_);
v_stop_boxed_5509_ = lean_unbox_usize(v_stop_5506_);
lean_dec(v_stop_5506_);
v_res_5510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5504_, v_i_boxed_5508_, v_stop_boxed_5509_, v_b_5507_);
lean_dec_ref(v_as_5504_);
return v_res_5510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5511_, size_t v_i_5512_, size_t v_stop_5513_, lean_object* v_b_5514_){
_start:
{
lean_object* v___y_5516_; uint8_t v___x_5520_; 
v___x_5520_ = lean_usize_dec_eq(v_i_5512_, v_stop_5513_);
if (v___x_5520_ == 0)
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; 
v___x_5521_ = lean_array_uget_borrowed(v_as_5511_, v_i_5512_);
v___x_5522_ = lean_unsigned_to_nat(0u);
v___x_5523_ = lean_array_get_size(v___x_5521_);
v___x_5524_ = lean_nat_dec_lt(v___x_5522_, v___x_5523_);
if (v___x_5524_ == 0)
{
v___y_5516_ = v_b_5514_;
goto v___jp_5515_;
}
else
{
uint8_t v___x_5525_; 
v___x_5525_ = lean_nat_dec_le(v___x_5523_, v___x_5523_);
if (v___x_5525_ == 0)
{
if (v___x_5524_ == 0)
{
v___y_5516_ = v_b_5514_;
goto v___jp_5515_;
}
else
{
size_t v___x_5526_; size_t v___x_5527_; lean_object* v___x_5528_; 
v___x_5526_ = ((size_t)0ULL);
v___x_5527_ = lean_usize_of_nat(v___x_5523_);
v___x_5528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5521_, v___x_5526_, v___x_5527_, v_b_5514_);
v___y_5516_ = v___x_5528_;
goto v___jp_5515_;
}
}
else
{
size_t v___x_5529_; size_t v___x_5530_; lean_object* v___x_5531_; 
v___x_5529_ = ((size_t)0ULL);
v___x_5530_ = lean_usize_of_nat(v___x_5523_);
v___x_5531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5521_, v___x_5529_, v___x_5530_, v_b_5514_);
v___y_5516_ = v___x_5531_;
goto v___jp_5515_;
}
}
}
else
{
return v_b_5514_;
}
v___jp_5515_:
{
size_t v___x_5517_; size_t v___x_5518_; 
v___x_5517_ = ((size_t)1ULL);
v___x_5518_ = lean_usize_add(v_i_5512_, v___x_5517_);
v_i_5512_ = v___x_5518_;
v_b_5514_ = v___y_5516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5532_, lean_object* v_i_5533_, lean_object* v_stop_5534_, lean_object* v_b_5535_){
_start:
{
size_t v_i_boxed_5536_; size_t v_stop_boxed_5537_; lean_object* v_res_5538_; 
v_i_boxed_5536_ = lean_unbox_usize(v_i_5533_);
lean_dec(v_i_5533_);
v_stop_boxed_5537_ = lean_unbox_usize(v_stop_5534_);
lean_dec(v_stop_5534_);
v_res_5538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5532_, v_i_boxed_5536_, v_stop_boxed_5537_, v_b_5535_);
lean_dec_ref(v_as_5532_);
return v_res_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5539_, lean_object* v_as_5540_){
_start:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; uint8_t v___x_5543_; 
v___x_5541_ = lean_unsigned_to_nat(0u);
v___x_5542_ = lean_array_get_size(v_as_5540_);
v___x_5543_ = lean_nat_dec_lt(v___x_5541_, v___x_5542_);
if (v___x_5543_ == 0)
{
return v_initState_5539_;
}
else
{
uint8_t v___x_5544_; 
v___x_5544_ = lean_nat_dec_le(v___x_5542_, v___x_5542_);
if (v___x_5544_ == 0)
{
if (v___x_5543_ == 0)
{
return v_initState_5539_;
}
else
{
size_t v___x_5545_; size_t v___x_5546_; lean_object* v___x_5547_; 
v___x_5545_ = ((size_t)0ULL);
v___x_5546_ = lean_usize_of_nat(v___x_5542_);
v___x_5547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5540_, v___x_5545_, v___x_5546_, v_initState_5539_);
return v___x_5547_;
}
}
else
{
size_t v___x_5548_; size_t v___x_5549_; lean_object* v___x_5550_; 
v___x_5548_ = ((size_t)0ULL);
v___x_5549_ = lean_usize_of_nat(v___x_5542_);
v___x_5550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5540_, v___x_5548_, v___x_5549_, v_initState_5539_);
return v___x_5550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5551_, lean_object* v_as_5552_){
_start:
{
lean_object* v_res_5553_; 
v_res_5553_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5551_, v_as_5552_);
lean_dec_ref(v_as_5552_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5554_){
_start:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5555_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5556_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5555_, v_es_5554_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5557_);
lean_dec_ref(v_es_5557_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; 
v___x_5579_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5580_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5579_);
return v___x_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
lean_object* v___x_5587_; lean_object* v_nextMacroScope_5588_; lean_object* v_ngen_5589_; lean_object* v_auxDeclNGen_5590_; lean_object* v_traceState_5591_; lean_object* v_messages_5592_; lean_object* v_infoState_5593_; lean_object* v_snapshotTasks_5594_; lean_object* v_newDecls_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5621_; 
v___x_5587_ = lean_st_ref_take(v___y_5585_);
v_nextMacroScope_5588_ = lean_ctor_get(v___x_5587_, 1);
v_ngen_5589_ = lean_ctor_get(v___x_5587_, 2);
v_auxDeclNGen_5590_ = lean_ctor_get(v___x_5587_, 3);
v_traceState_5591_ = lean_ctor_get(v___x_5587_, 4);
v_messages_5592_ = lean_ctor_get(v___x_5587_, 6);
v_infoState_5593_ = lean_ctor_get(v___x_5587_, 7);
v_snapshotTasks_5594_ = lean_ctor_get(v___x_5587_, 8);
v_newDecls_5595_ = lean_ctor_get(v___x_5587_, 9);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5621_ == 0)
{
lean_object* v_unused_5622_; lean_object* v_unused_5623_; 
v_unused_5622_ = lean_ctor_get(v___x_5587_, 5);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v___x_5587_, 0);
lean_dec(v_unused_5623_);
v___x_5597_ = v___x_5587_;
v_isShared_5598_ = v_isSharedCheck_5621_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_newDecls_5595_);
lean_inc(v_snapshotTasks_5594_);
lean_inc(v_infoState_5593_);
lean_inc(v_messages_5592_);
lean_inc(v_traceState_5591_);
lean_inc(v_auxDeclNGen_5590_);
lean_inc(v_ngen_5589_);
lean_inc(v_nextMacroScope_5588_);
lean_dec(v___x_5587_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5621_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5599_; lean_object* v___x_5601_; 
v___x_5599_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 5, v___x_5599_);
lean_ctor_set(v___x_5597_, 0, v_env_5583_);
v___x_5601_ = v___x_5597_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_env_5583_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v_nextMacroScope_5588_);
lean_ctor_set(v_reuseFailAlloc_5620_, 2, v_ngen_5589_);
lean_ctor_set(v_reuseFailAlloc_5620_, 3, v_auxDeclNGen_5590_);
lean_ctor_set(v_reuseFailAlloc_5620_, 4, v_traceState_5591_);
lean_ctor_set(v_reuseFailAlloc_5620_, 5, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5620_, 6, v_messages_5592_);
lean_ctor_set(v_reuseFailAlloc_5620_, 7, v_infoState_5593_);
lean_ctor_set(v_reuseFailAlloc_5620_, 8, v_snapshotTasks_5594_);
lean_ctor_set(v_reuseFailAlloc_5620_, 9, v_newDecls_5595_);
v___x_5601_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v_mctx_5604_; lean_object* v_zetaDeltaFVarIds_5605_; lean_object* v_postponed_5606_; lean_object* v_diag_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5618_; 
v___x_5602_ = lean_st_ref_set(v___y_5585_, v___x_5601_);
v___x_5603_ = lean_st_ref_take(v___y_5584_);
v_mctx_5604_ = lean_ctor_get(v___x_5603_, 0);
v_zetaDeltaFVarIds_5605_ = lean_ctor_get(v___x_5603_, 2);
v_postponed_5606_ = lean_ctor_get(v___x_5603_, 3);
v_diag_5607_ = lean_ctor_get(v___x_5603_, 4);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5618_ == 0)
{
lean_object* v_unused_5619_; 
v_unused_5619_ = lean_ctor_get(v___x_5603_, 1);
lean_dec(v_unused_5619_);
v___x_5609_ = v___x_5603_;
v_isShared_5610_ = v_isSharedCheck_5618_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_diag_5607_);
lean_inc(v_postponed_5606_);
lean_inc(v_zetaDeltaFVarIds_5605_);
lean_inc(v_mctx_5604_);
lean_dec(v___x_5603_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5618_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5611_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5611_);
v___x_5613_ = v___x_5609_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_mctx_5604_);
lean_ctor_set(v_reuseFailAlloc_5617_, 1, v___x_5611_);
lean_ctor_set(v_reuseFailAlloc_5617_, 2, v_zetaDeltaFVarIds_5605_);
lean_ctor_set(v_reuseFailAlloc_5617_, 3, v_postponed_5606_);
lean_ctor_set(v_reuseFailAlloc_5617_, 4, v_diag_5607_);
v___x_5613_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v___x_5614_ = lean_st_ref_set(v___y_5584_, v___x_5613_);
v___x_5615_ = lean_box(0);
v___x_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
return v___x_5616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v_res_5628_; 
v_res_5628_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5624_, v___y_5625_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec(v___y_5625_);
return v_res_5628_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_){
_start:
{
lean_object* v___x_5635_; 
v___x_5635_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5629_, v___y_5631_, v___y_5633_);
return v___x_5635_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v_res_5642_; 
v_res_5642_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
return v_res_5642_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5644_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5645_ = l_Lean_stringToMessageData(v___x_5644_);
return v___x_5645_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5648_ = l_Lean_stringToMessageData(v___x_5647_);
return v___x_5648_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5650_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5651_ = l_Lean_stringToMessageData(v___x_5650_);
return v___x_5651_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5653_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5654_ = l_Lean_stringToMessageData(v___x_5653_);
return v___x_5654_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5656_; lean_object* v___x_5657_; 
v___x_5656_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5657_ = l_Lean_stringToMessageData(v___x_5656_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5658_, lean_object* v_prio_5659_, lean_object* v_x_5660_, lean_object* v_type_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v___x_5667_; 
v___x_5667_ = l_Lean_Expr_getAppFn(v_type_5661_);
if (lean_obj_tag(v___x_5667_) == 4)
{
lean_object* v_declName_5668_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___x_5683_; lean_object* v_env_5684_; uint8_t v___x_5685_; 
v_declName_5668_ = lean_ctor_get(v___x_5667_, 0);
lean_inc_n(v_declName_5668_, 2);
lean_dec_ref(v___x_5667_);
v___x_5683_ = lean_st_ref_get(v___y_5665_);
v_env_5684_ = lean_ctor_get(v___x_5683_, 0);
lean_inc_ref(v_env_5684_);
lean_dec(v___x_5683_);
v___x_5685_ = lean_is_class(v_env_5684_, v_declName_5668_);
if (v___x_5685_ == 0)
{
lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
lean_dec(v_prio_5659_);
v___x_5686_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5687_ = l_Lean_MessageData_ofConstName(v_declName_5658_, v___x_5685_);
v___x_5688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5688_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
lean_inc(v_declName_5668_);
v___x_5691_ = l_Lean_MessageData_ofName(v_declName_5668_);
v___x_5692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5690_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
v___x_5693_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = l_Lean_MessageData_ofConstName(v_declName_5668_, v___x_5685_);
v___x_5696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5694_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5698_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
return v___x_5699_;
}
else
{
v___y_5670_ = v___y_5662_;
v___y_5671_ = v___y_5663_;
v___y_5672_ = v___y_5664_;
v___y_5673_ = v___y_5665_;
goto v___jp_5669_;
}
v___jp_5669_:
{
lean_object* v___x_5674_; lean_object* v_env_5675_; lean_object* v___x_5676_; lean_object* v_toEnvExtension_5677_; lean_object* v_asyncMode_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; 
v___x_5674_ = lean_st_ref_get(v___y_5673_);
v_env_5675_ = lean_ctor_get(v___x_5674_, 0);
lean_inc_ref(v_env_5675_);
lean_dec(v___x_5674_);
v___x_5676_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5677_ = lean_ctor_get(v___x_5676_, 0);
v_asyncMode_5678_ = lean_ctor_get(v_toEnvExtension_5677_, 2);
v___x_5679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5679_, 0, v_declName_5668_);
lean_ctor_set(v___x_5679_, 1, v_declName_5658_);
lean_ctor_set(v___x_5679_, 2, v_prio_5659_);
v___x_5680_ = lean_box(0);
v___x_5681_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5676_, v_env_5675_, v___x_5679_, v_asyncMode_5678_, v___x_5680_);
v___x_5682_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5681_, v___y_5671_, v___y_5673_);
return v___x_5682_;
}
}
else
{
lean_object* v___x_5700_; uint8_t v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
lean_dec_ref(v___x_5667_);
lean_dec(v_prio_5659_);
v___x_5700_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5701_ = 0;
v___x_5702_ = l_Lean_MessageData_ofConstName(v_declName_5658_, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5700_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v___x_5704_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5703_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5705_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
return v___x_5706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5707_, lean_object* v_prio_5708_, lean_object* v_x_5709_, lean_object* v_type_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v_res_5716_; 
v_res_5716_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5707_, v_prio_5708_, v_x_5709_, v_type_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec_ref(v_type_5710_);
lean_dec_ref(v_x_5709_);
return v_res_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5717_, lean_object* v_prio_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_){
_start:
{
lean_object* v___x_5724_; lean_object* v_env_5725_; uint8_t v___x_5726_; lean_object* v___x_5727_; 
v___x_5724_ = lean_st_ref_get(v_a_5722_);
v_env_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc_ref(v_env_5725_);
lean_dec(v___x_5724_);
v___x_5726_ = 0;
lean_inc(v_declName_5717_);
v___x_5727_ = l_Lean_Environment_find_x3f(v_env_5725_, v_declName_5717_, v___x_5726_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
lean_dec(v_prio_5718_);
v___x_5728_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5729_ = l_Lean_MessageData_ofConstName(v_declName_5717_, v___x_5726_);
v___x_5730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5732_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_);
return v___x_5733_;
}
else
{
lean_object* v_val_5734_; lean_object* v___f_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_val_5734_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_val_5734_);
lean_dec_ref(v___x_5727_);
v___f_5735_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5735_, 0, v_declName_5717_);
lean_closure_set(v___f_5735_, 1, v_prio_5718_);
v___x_5736_ = l_Lean_ConstantInfo_type(v_val_5734_);
lean_dec(v_val_5734_);
v___x_5737_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5736_, v___f_5735_, v___x_5726_, v___x_5726_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_);
return v___x_5737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5738_, lean_object* v_prio_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_){
_start:
{
lean_object* v_res_5745_; 
v_res_5745_ = l_Lean_Meta_addDefaultInstance(v_declName_5738_, v_prio_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
return v_res_5745_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; 
v___x_5747_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5748_ = l_Lean_stringToMessageData(v___x_5747_);
return v___x_5748_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5750_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5751_ = l_Lean_stringToMessageData(v___x_5750_);
return v___x_5751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5755_, uint8_t v_kind_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___y_5766_; 
v___x_5760_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5761_ = l_Lean_MessageData_ofName(v_name_5755_);
v___x_5762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5762_);
lean_ctor_set(v___x_5764_, 1, v___x_5763_);
switch(v_kind_5756_)
{
case 0:
{
lean_object* v___x_5773_; 
v___x_5773_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5766_ = v___x_5773_;
goto v___jp_5765_;
}
case 1:
{
lean_object* v___x_5774_; 
v___x_5774_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5766_ = v___x_5774_;
goto v___jp_5765_;
}
default: 
{
lean_object* v___x_5775_; 
v___x_5775_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5766_ = v___x_5775_;
goto v___jp_5765_;
}
}
v___jp_5765_:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; 
lean_inc_ref(v___y_5766_);
v___x_5767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5767_, 0, v___y_5766_);
v___x_5768_ = l_Lean_MessageData_ofFormat(v___x_5767_);
v___x_5769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5764_);
lean_ctor_set(v___x_5769_, 1, v___x_5768_);
v___x_5770_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5771_, 0, v___x_5769_);
lean_ctor_set(v___x_5771_, 1, v___x_5770_);
v___x_5772_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5771_, v___y_5757_, v___y_5758_);
return v___x_5772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5776_, lean_object* v_kind_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
uint8_t v_kind_boxed_5781_; lean_object* v_res_5782_; 
v_kind_boxed_5781_ = lean_unbox(v_kind_5777_);
v_res_5782_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5776_, v_kind_boxed_5781_, v___y_5778_, v___y_5779_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
return v_res_5782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5783_, lean_object* v___x_5784_, lean_object* v___x_5785_, lean_object* v_declName_5786_, lean_object* v_stx_5787_, uint8_t v_kind_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5792_ = lean_unsigned_to_nat(1u);
v___x_5793_ = l_Lean_Syntax_getArg(v_stx_5787_, v___x_5792_);
v___x_5794_ = l_Lean_getAttrParamOptPrio(v___x_5793_, v___y_5789_, v___y_5790_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v_a_5795_; lean_object* v___y_5797_; lean_object* v___y_5798_; uint8_t v___x_5829_; uint8_t v___x_5830_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
lean_inc(v_a_5795_);
lean_dec_ref(v___x_5794_);
v___x_5829_ = 0;
v___x_5830_ = l_Lean_instBEqAttributeKind_beq(v_kind_5788_, v___x_5829_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; 
lean_dec(v_a_5795_);
lean_dec(v_declName_5786_);
lean_dec(v___x_5784_);
lean_dec(v___x_5783_);
v___x_5831_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5785_, v_kind_5788_, v___y_5789_, v___y_5790_);
return v___x_5831_;
}
else
{
lean_dec(v___x_5785_);
v___y_5797_ = v___y_5789_;
v___y_5798_ = v___y_5790_;
goto v___jp_5796_;
}
v___jp_5796_:
{
uint8_t v___x_5799_; uint8_t v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; size_t v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5799_ = 0;
v___x_5800_ = 1;
v___x_5801_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5802_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5803_ = lean_unsigned_to_nat(32u);
v___x_5804_ = lean_mk_empty_array_with_capacity(v___x_5803_);
v___x_5805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5806_ = ((size_t)5ULL);
lean_inc_n(v___x_5783_, 6);
v___x_5807_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5807_, 0, v___x_5805_);
lean_ctor_set(v___x_5807_, 1, v___x_5804_);
lean_ctor_set(v___x_5807_, 2, v___x_5783_);
lean_ctor_set(v___x_5807_, 3, v___x_5783_);
lean_ctor_set_usize(v___x_5807_, 4, v___x_5806_);
v___x_5808_ = lean_box(1);
lean_inc_ref(v___x_5807_);
v___x_5809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5802_);
lean_ctor_set(v___x_5809_, 1, v___x_5807_);
lean_ctor_set(v___x_5809_, 2, v___x_5808_);
v___x_5810_ = lean_mk_empty_array_with_capacity(v___x_5783_);
v___x_5811_ = lean_box(0);
lean_inc(v___x_5784_);
v___x_5812_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5812_, 0, v___x_5801_);
lean_ctor_set(v___x_5812_, 1, v___x_5784_);
lean_ctor_set(v___x_5812_, 2, v___x_5809_);
lean_ctor_set(v___x_5812_, 3, v___x_5810_);
lean_ctor_set(v___x_5812_, 4, v___x_5811_);
lean_ctor_set(v___x_5812_, 5, v___x_5783_);
lean_ctor_set(v___x_5812_, 6, v___x_5811_);
lean_ctor_set_uint8(v___x_5812_, sizeof(void*)*7, v___x_5799_);
lean_ctor_set_uint8(v___x_5812_, sizeof(void*)*7 + 1, v___x_5799_);
lean_ctor_set_uint8(v___x_5812_, sizeof(void*)*7 + 2, v___x_5799_);
lean_ctor_set_uint8(v___x_5812_, sizeof(void*)*7 + 3, v___x_5800_);
v___x_5813_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5783_);
lean_ctor_set(v___x_5813_, 1, v___x_5783_);
lean_ctor_set(v___x_5813_, 2, v___x_5783_);
lean_ctor_set(v___x_5813_, 3, v___x_5783_);
lean_ctor_set(v___x_5813_, 4, v___x_5802_);
lean_ctor_set(v___x_5813_, 5, v___x_5802_);
lean_ctor_set(v___x_5813_, 6, v___x_5802_);
lean_ctor_set(v___x_5813_, 7, v___x_5802_);
lean_ctor_set(v___x_5813_, 8, v___x_5802_);
lean_ctor_set(v___x_5813_, 9, v___x_5802_);
v___x_5814_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5815_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5816_, 0, v___x_5813_);
lean_ctor_set(v___x_5816_, 1, v___x_5814_);
lean_ctor_set(v___x_5816_, 2, v___x_5784_);
lean_ctor_set(v___x_5816_, 3, v___x_5807_);
lean_ctor_set(v___x_5816_, 4, v___x_5815_);
v___x_5817_ = lean_st_mk_ref(v___x_5816_);
v___x_5818_ = l_Lean_Meta_addDefaultInstance(v_declName_5786_, v_a_5795_, v___x_5812_, v___x_5817_, v___y_5797_, v___y_5798_);
lean_dec_ref(v___x_5812_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5827_; 
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; 
v_unused_5828_ = lean_ctor_get(v___x_5818_, 0);
lean_dec(v_unused_5828_);
v___x_5820_ = v___x_5818_;
v_isShared_5821_ = v_isSharedCheck_5827_;
goto v_resetjp_5819_;
}
else
{
lean_dec(v___x_5818_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5827_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5825_; 
v___x_5822_ = lean_st_ref_get(v___x_5817_);
lean_dec(v___x_5817_);
lean_dec(v___x_5822_);
v___x_5823_ = lean_box(0);
if (v_isShared_5821_ == 0)
{
lean_ctor_set(v___x_5820_, 0, v___x_5823_);
v___x_5825_ = v___x_5820_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5823_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
else
{
lean_dec(v___x_5817_);
return v___x_5818_;
}
}
}
else
{
lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5839_; 
lean_dec(v_declName_5786_);
lean_dec(v___x_5785_);
lean_dec(v___x_5784_);
lean_dec(v___x_5783_);
v_a_5832_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5834_ = v___x_5794_;
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5794_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v___x_5837_; 
if (v_isShared_5835_ == 0)
{
v___x_5837_ = v___x_5834_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_a_5832_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5840_, lean_object* v___x_5841_, lean_object* v___x_5842_, lean_object* v_declName_5843_, lean_object* v_stx_5844_, lean_object* v_kind_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
uint8_t v_kind_boxed_5849_; lean_object* v_res_5850_; 
v_kind_boxed_5849_ = lean_unbox(v_kind_5845_);
v_res_5850_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5840_, v___x_5841_, v___x_5842_, v_declName_5843_, v_stx_5844_, v_kind_boxed_5849_, v___y_5846_, v___y_5847_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v_stx_5844_);
return v_res_5850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5853_ = l_Lean_stringToMessageData(v___x_5852_);
return v___x_5853_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5856_ = l_Lean_stringToMessageData(v___x_5855_);
return v___x_5856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5857_, lean_object* v_decl_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5862_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5863_ = l_Lean_MessageData_ofName(v___x_5857_);
v___x_5864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5862_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5864_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
v___x_5867_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5866_, v___y_5859_, v___y_5860_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5868_, lean_object* v_decl_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_){
_start:
{
lean_object* v_res_5873_; 
v_res_5873_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5868_, v_decl_5869_, v___y_5870_, v___y_5871_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v_decl_5869_);
return v_res_5873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5906_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5907_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5908_ = l_Lean_registerBuiltinAttribute(v___x_5907_);
if (lean_obj_tag(v___x_5908_) == 0)
{
lean_object* v___x_5909_; uint8_t v___x_5910_; lean_object* v___x_5911_; 
lean_dec_ref(v___x_5908_);
v___x_5909_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5910_ = 0;
v___x_5911_ = l_Lean_registerTraceClass(v___x_5909_, v___x_5910_, v___x_5906_);
return v___x_5911_;
}
else
{
return v___x_5908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5912_){
_start:
{
lean_object* v_res_5913_; 
v_res_5913_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5914_, lean_object* v_name_5915_, uint8_t v_kind_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v___x_5920_; 
v___x_5920_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5915_, v_kind_5916_, v___y_5917_, v___y_5918_);
return v___x_5920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5921_, lean_object* v_name_5922_, lean_object* v_kind_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_){
_start:
{
uint8_t v_kind_boxed_5927_; lean_object* v_res_5928_; 
v_kind_boxed_5927_ = lean_unbox(v_kind_5923_);
v_res_5928_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5921_, v_name_5922_, v_kind_boxed_5927_, v___y_5924_, v___y_5925_);
lean_dec(v___y_5925_);
lean_dec_ref(v___y_5924_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5929_, lean_object* v_toPure_5930_, lean_object* v_____do__lift_5931_){
_start:
{
lean_object* v___x_5932_; lean_object* v_toEnvExtension_5933_; lean_object* v_asyncMode_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v_priorities_5937_; lean_object* v___x_5938_; 
v___x_5932_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5933_ = lean_ctor_get(v___x_5932_, 0);
v_asyncMode_5934_ = lean_ctor_get(v_toEnvExtension_5933_, 2);
v___x_5935_ = lean_box(0);
v___x_5936_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5929_, v___x_5932_, v_____do__lift_5931_, v_asyncMode_5934_, v___x_5935_);
v_priorities_5937_ = lean_ctor_get(v___x_5936_, 1);
lean_inc(v_priorities_5937_);
lean_dec(v___x_5936_);
v___x_5938_ = lean_apply_2(v_toPure_5930_, lean_box(0), v_priorities_5937_);
return v___x_5938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5939_, lean_object* v_inst_5940_){
_start:
{
lean_object* v_toApplicative_5941_; lean_object* v_toBind_5942_; lean_object* v_getEnv_5943_; lean_object* v_toPure_5944_; lean_object* v___x_5945_; lean_object* v___f_5946_; lean_object* v___x_5947_; 
v_toApplicative_5941_ = lean_ctor_get(v_inst_5939_, 0);
lean_inc_ref(v_toApplicative_5941_);
v_toBind_5942_ = lean_ctor_get(v_inst_5939_, 1);
lean_inc(v_toBind_5942_);
lean_dec_ref(v_inst_5939_);
v_getEnv_5943_ = lean_ctor_get(v_inst_5940_, 0);
lean_inc(v_getEnv_5943_);
lean_dec_ref(v_inst_5940_);
v_toPure_5944_ = lean_ctor_get(v_toApplicative_5941_, 1);
lean_inc(v_toPure_5944_);
lean_dec_ref(v_toApplicative_5941_);
v___x_5945_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5946_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5946_, 0, v___x_5945_);
lean_closure_set(v___f_5946_, 1, v_toPure_5944_);
v___x_5947_ = lean_apply_4(v_toBind_5942_, lean_box(0), lean_box(0), v_getEnv_5943_, v___f_5946_);
return v___x_5947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5948_, lean_object* v_inst_5949_, lean_object* v_inst_5950_){
_start:
{
lean_object* v___x_5951_; 
v___x_5951_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5949_, v_inst_5950_);
return v___x_5951_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_5952_, uint8_t v_isExporting_5953_, lean_object* v_x_5954_){
_start:
{
lean_object* v_fst_5955_; uint8_t v___x_5956_; 
v_fst_5955_ = lean_ctor_get(v_x_5954_, 0);
lean_inc(v_fst_5955_);
lean_dec_ref(v_x_5954_);
v___x_5956_ = l_Lean_Environment_contains(v_env_5952_, v_fst_5955_, v_isExporting_5953_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_5957_, lean_object* v_isExporting_5958_, lean_object* v_x_5959_){
_start:
{
uint8_t v_isExporting_boxed_5960_; uint8_t v_res_5961_; lean_object* v_r_5962_; 
v_isExporting_boxed_5960_ = lean_unbox(v_isExporting_5958_);
v_res_5961_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_5957_, v_isExporting_boxed_5960_, v_x_5959_);
v_r_5962_ = lean_box(v_res_5961_);
return v_r_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_5963_, lean_object* v_toApplicative_5964_, lean_object* v_className_5965_, lean_object* v_env_5966_){
_start:
{
lean_object* v___y_5968_; lean_object* v___x_5978_; lean_object* v_toEnvExtension_5979_; lean_object* v_asyncMode_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v_defaultInstances_5983_; lean_object* v___x_5984_; 
v___x_5978_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5979_ = lean_ctor_get(v___x_5978_, 0);
v_asyncMode_5980_ = lean_ctor_get(v_toEnvExtension_5979_, 2);
v___x_5981_ = lean_box(0);
lean_inc_ref(v_env_5966_);
v___x_5982_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5963_, v___x_5978_, v_env_5966_, v_asyncMode_5980_, v___x_5981_);
v_defaultInstances_5983_ = lean_ctor_get(v___x_5982_, 0);
lean_inc(v_defaultInstances_5983_);
lean_dec(v___x_5982_);
v___x_5984_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5983_, v_className_5965_);
lean_dec(v_defaultInstances_5983_);
if (lean_obj_tag(v___x_5984_) == 0)
{
lean_object* v___x_5985_; 
v___x_5985_ = lean_box(0);
v___y_5968_ = v___x_5985_;
goto v___jp_5967_;
}
else
{
lean_object* v_val_5986_; 
v_val_5986_ = lean_ctor_get(v___x_5984_, 0);
lean_inc(v_val_5986_);
lean_dec_ref(v___x_5984_);
v___y_5968_ = v_val_5986_;
goto v___jp_5967_;
}
v___jp_5967_:
{
uint8_t v_isExporting_5969_; 
v_isExporting_5969_ = lean_ctor_get_uint8(v_env_5966_, sizeof(void*)*8);
if (v_isExporting_5969_ == 0)
{
lean_object* v_toPure_5970_; lean_object* v___x_5971_; 
lean_dec_ref(v_env_5966_);
v_toPure_5970_ = lean_ctor_get(v_toApplicative_5964_, 1);
lean_inc(v_toPure_5970_);
lean_dec_ref(v_toApplicative_5964_);
v___x_5971_ = lean_apply_2(v_toPure_5970_, lean_box(0), v___y_5968_);
return v___x_5971_;
}
else
{
lean_object* v_toPure_5972_; lean_object* v___x_5973_; lean_object* v___f_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v_toPure_5972_ = lean_ctor_get(v_toApplicative_5964_, 1);
lean_inc(v_toPure_5972_);
lean_dec_ref(v_toApplicative_5964_);
v___x_5973_ = lean_box(v_isExporting_5969_);
v___f_5974_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_5974_, 0, v_env_5966_);
lean_closure_set(v___f_5974_, 1, v___x_5973_);
v___x_5975_ = lean_box(0);
v___x_5976_ = l_List_filterTR_loop___redArg(v___f_5974_, v___y_5968_, v___x_5975_);
v___x_5977_ = lean_apply_2(v_toPure_5972_, lean_box(0), v___x_5976_);
return v___x_5977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_5987_, lean_object* v_toApplicative_5988_, lean_object* v_className_5989_, lean_object* v_env_5990_){
_start:
{
lean_object* v_res_5991_; 
v_res_5991_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_5987_, v_toApplicative_5988_, v_className_5989_, v_env_5990_);
lean_dec(v_className_5989_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5992_, lean_object* v_inst_5993_, lean_object* v_className_5994_){
_start:
{
lean_object* v_toApplicative_5995_; lean_object* v_toBind_5996_; lean_object* v_getEnv_5997_; lean_object* v___x_5998_; lean_object* v___f_5999_; lean_object* v___x_6000_; 
v_toApplicative_5995_ = lean_ctor_get(v_inst_5992_, 0);
lean_inc_ref(v_toApplicative_5995_);
v_toBind_5996_ = lean_ctor_get(v_inst_5992_, 1);
lean_inc(v_toBind_5996_);
lean_dec_ref(v_inst_5992_);
v_getEnv_5997_ = lean_ctor_get(v_inst_5993_, 0);
lean_inc(v_getEnv_5997_);
lean_dec_ref(v_inst_5993_);
v___x_5998_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5999_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_5999_, 0, v___x_5998_);
lean_closure_set(v___f_5999_, 1, v_toApplicative_5995_);
lean_closure_set(v___f_5999_, 2, v_className_5994_);
v___x_6000_ = lean_apply_4(v_toBind_5996_, lean_box(0), lean_box(0), v_getEnv_5997_, v___f_5999_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6001_, lean_object* v_inst_6002_, lean_object* v_inst_6003_, lean_object* v_className_6004_){
_start:
{
lean_object* v___x_6005_; 
v___x_6005_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6002_, v_inst_6003_, v_className_6004_);
return v___x_6005_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin);
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
