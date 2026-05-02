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
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
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
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 253, 187, 89, 234, 162, 232, 19)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0_value)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "cannot find synthesization order for instance "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " with type"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "\nall remaining arguments have metavariables:"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "defaultInstanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 56, 120, 160, 178, 206, 131, 123)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addDefaultInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t v_level_1090_, lean_object* v_e_1091_){
_start:
{
uint8_t v___y_1093_; uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = 2;
v___x_1097_ = l_Lean_instDecidableEqOLeanLevel(v_level_1090_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v_globalName_x3f_1098_; 
v_globalName_x3f_1098_ = lean_ctor_get(v_e_1091_, 3);
lean_inc(v_globalName_x3f_1098_);
if (lean_obj_tag(v_globalName_x3f_1098_) == 0)
{
v___y_1093_ = v___x_1097_;
goto v___jp_1092_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
v_val_1099_ = lean_ctor_get(v_globalName_x3f_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_globalName_x3f_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1101_ = v_globalName_x3f_1098_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v_globalName_x3f_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_isPrivateName(v_val_1099_);
lean_dec(v_val_1099_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1105_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_e_1091_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_e_1091_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_del_object(v___x_1101_);
v___y_1093_ = v___x_1097_;
goto v___jp_1092_;
}
}
}
}
else
{
v___y_1093_ = v___x_1097_;
goto v___jp_1092_;
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_e_1091_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_e_1091_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_level_1108_, lean_object* v_e_1109_){
_start:
{
uint8_t v_level_boxed_1110_; lean_object* v_res_1111_; 
v_level_boxed_1110_ = lean_unbox(v_level_1108_);
v_res_1111_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v_level_boxed_1110_, v_e_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object* v___y_1112_){
_start:
{
lean_inc_ref(v___y_1112_);
return v___y_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v___y_1113_);
lean_dec_ref(v___y_1113_);
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___f_1123_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___f_1124_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1125_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1126_);
lean_ctor_set(v___x_1128_, 2, v___x_1125_);
lean_ctor_set(v___x_1128_, 3, v___f_1124_);
lean_ctor_set(v___x_1128_, 4, v___f_1123_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1131_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1134_, uint8_t v_allowLevelAssignments_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1135_, v_k_1134_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1158_, lean_object* v_allowLevelAssignments_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1165_; lean_object* v_res_1166_; 
v_allowLevelAssignments_boxed_1165_ = lean_unbox(v_allowLevelAssignments_1159_);
v_res_1166_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1158_, v_allowLevelAssignments_boxed_1165_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1167_, lean_object* v_k_1168_, uint8_t v_allowLevelAssignments_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1168_, v_allowLevelAssignments_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_k_1177_, lean_object* v_allowLevelAssignments_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1184_; lean_object* v_res_1185_; 
v_allowLevelAssignments_boxed_1184_ = lean_unbox(v_allowLevelAssignments_1178_);
v_res_1185_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1176_, v_k_1177_, v_allowLevelAssignments_boxed_1184_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1186_, lean_object* v___x_1187_, uint8_t v___x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1186_, v___x_1187_, v___x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_snd_1196_; lean_object* v_snd_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v___x_1194_);
v_snd_1196_ = lean_ctor_get(v_a_1195_, 1);
lean_inc(v_snd_1196_);
lean_dec(v_a_1195_);
v_snd_1197_ = lean_ctor_get(v_snd_1196_, 1);
lean_inc(v_snd_1197_);
lean_dec(v_snd_1196_);
v___x_1198_ = 0;
v___x_1199_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1197_, v___x_1198_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1199_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_497__boxed_1216_; lean_object* v_res_1217_; 
v___x_497__boxed_1216_ = lean_unbox(v___x_1210_);
v_res_1217_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1208_, v___x_1209_, v___x_497__boxed_1216_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc(v_a_1222_);
lean_inc_ref(v_a_1221_);
lean_inc(v_a_1220_);
lean_inc_ref(v_a_1219_);
v___x_1224_ = lean_infer_type(v_e_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = lean_box(0);
v___x_1227_ = 0;
v___x_1228_ = lean_box(v___x_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1229_, 0, v_a_1225_);
lean_closure_set(v___f_1229_, 1, v___x_1226_);
lean_closure_set(v___f_1229_, 2, v___x_1228_);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1229_, v___x_1230_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1231_;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1247_, lean_object* v_b_1248_, lean_object* v_c_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
v___x_1255_ = lean_apply_7(v_k_1247_, v_b_1248_, v_c_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, lean_box(0));
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1256_, lean_object* v_b_1257_, lean_object* v_c_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1256_, v_b_1257_, v_c_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1265_, lean_object* v_k_1266_, uint8_t v_cleanupAnnotations_1267_, uint8_t v_whnfType_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; 
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1274_, 0, v_k_1266_);
v___x_1275_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1265_, v___f_1274_, v_cleanupAnnotations_1267_, v_whnfType_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1275_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1292_, lean_object* v_k_1293_, lean_object* v_cleanupAnnotations_1294_, lean_object* v_whnfType_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1301_; uint8_t v_whnfType_boxed_1302_; lean_object* v_res_1303_; 
v_cleanupAnnotations_boxed_1301_ = lean_unbox(v_cleanupAnnotations_1294_);
v_whnfType_boxed_1302_ = lean_unbox(v_whnfType_1295_);
v_res_1303_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1292_, v_k_1293_, v_cleanupAnnotations_boxed_1301_, v_whnfType_boxed_1302_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1304_, lean_object* v_type_1305_, lean_object* v_k_1306_, uint8_t v_cleanupAnnotations_1307_, uint8_t v_whnfType_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1305_, v_k_1306_, v_cleanupAnnotations_1307_, v_whnfType_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_type_1316_, lean_object* v_k_1317_, lean_object* v_cleanupAnnotations_1318_, lean_object* v_whnfType_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1325_; uint8_t v_whnfType_boxed_1326_; lean_object* v_res_1327_; 
v_cleanupAnnotations_boxed_1325_ = lean_unbox(v_cleanupAnnotations_1318_);
v_whnfType_boxed_1326_ = lean_unbox(v_whnfType_1319_);
v_res_1327_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1315_, v_type_1316_, v_k_1317_, v_cleanupAnnotations_boxed_1325_, v_whnfType_boxed_1326_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1331_, size_t v_sz_1332_, size_t v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1333_, v_sz_1332_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_b_1334_);
return v___x_1341_;
}
else
{
lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1395_; 
v_fst_1342_ = lean_ctor_get(v_b_1334_, 0);
v_snd_1343_ = lean_ctor_get(v_b_1334_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_b_1334_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1345_ = v_b_1334_;
v_isShared_1346_ = v_isSharedCheck_1395_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_inc(v_fst_1342_);
lean_dec(v_b_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1395_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_next_1352_; 
v_next_1352_ = lean_ctor_get(v_snd_1343_, 0);
lean_inc(v_next_1352_);
if (lean_obj_tag(v_next_1352_) == 0)
{
goto v___jp_1347_;
}
else
{
lean_object* v_upperBound_1353_; lean_object* v_val_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1394_; 
v_upperBound_1353_ = lean_ctor_get(v_snd_1343_, 1);
v_val_1354_ = lean_ctor_get(v_next_1352_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_next_1352_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1356_ = v_next_1352_;
v_isShared_1357_ = v_isSharedCheck_1394_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_val_1354_);
lean_dec(v_next_1352_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1394_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_nat_dec_lt(v_val_1354_, v_upperBound_1353_);
if (v___x_1358_ == 0)
{
lean_del_object(v___x_1356_);
lean_dec(v_val_1354_);
goto v___jp_1347_;
}
else
{
lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1391_; 
lean_inc(v_upperBound_1353_);
lean_del_object(v___x_1345_);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_snd_1343_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; 
v_unused_1392_ = lean_ctor_get(v_snd_1343_, 1);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_snd_1343_, 0);
lean_dec(v_unused_1393_);
v___x_1360_ = v_snd_1343_;
v_isShared_1361_ = v_isSharedCheck_1391_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v_snd_1343_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1391_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_array_uget_borrowed(v_as_1331_, v_i_1333_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v_a_1362_);
v___x_1363_ = lean_infer_type(v_a_1362_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_a_1366_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_val_1354_, v___x_1370_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1371_);
v___x_1373_ = v___x_1356_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1372_;
}
v___jp_1365_:
{
size_t v___x_1367_; size_t v___x_1368_; 
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1333_, v___x_1367_);
v_i_1333_ = v___x_1368_;
v_b_1334_ = v_a_1366_;
goto _start;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1373_);
v___x_1375_ = v___x_1360_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_upperBound_1353_);
v___x_1375_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1377_ = l_Lean_Expr_isAppOf(v_a_1364_, v___x_1376_);
lean_dec(v_a_1364_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec(v_val_1354_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_fst_1342_);
lean_ctor_set(v___x_1378_, 1, v___x_1375_);
v_a_1366_ = v___x_1378_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_array_push(v_fst_1342_, v_val_1354_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1375_);
v_a_1366_ = v___x_1380_;
goto v___jp_1365_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_del_object(v___x_1360_);
lean_del_object(v___x_1356_);
lean_dec(v_val_1354_);
lean_dec(v_upperBound_1353_);
lean_dec(v_fst_1342_);
v_a_1383_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1363_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1363_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
}
v___jp_1347_:
{
lean_object* v___x_1349_; 
if (v_isShared_1346_ == 0)
{
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_fst_1342_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_snd_1343_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1396_, lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_b_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
size_t v_sz_boxed_1405_; size_t v_i_boxed_1406_; lean_object* v_res_1407_; 
v_sz_boxed_1405_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1406_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1396_, v_sz_boxed_1405_, v_i_boxed_1406_, v_b_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec_ref(v_as_1396_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1412_, lean_object* v_args_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___y_1422_; lean_object* v_env_1447_; lean_object* v___x_1448_; 
v___x_1420_ = lean_st_ref_get(v___y_1418_);
v_env_1447_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_ref(v_env_1447_);
lean_dec(v___x_1420_);
v___x_1448_ = l_Lean_getOutParamPositions_x3f(v_env_1447_, v_declName_1412_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1422_ = v___x_1449_;
goto v___jp_1421_;
}
else
{
lean_object* v_val_1450_; 
v_val_1450_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_val_1450_);
lean_dec_ref(v___x_1448_);
v___y_1422_ = v_val_1450_;
goto v___jp_1421_;
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; size_t v_sz_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1423_ = lean_array_get_size(v_args_1413_);
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1423_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1422_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v_sz_1427_ = lean_array_size(v_args_1413_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1413_, v_sz_1427_, v___x_1428_, v___x_1426_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_fst_1434_; lean_object* v___x_1436_; 
v_fst_1434_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_fst_1434_);
lean_dec(v_a_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_fst_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_fst_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1429_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1429_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1451_, lean_object* v_args_1452_, lean_object* v_x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1451_, v_args_1452_, v_x_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v_x_1453_);
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Expr_getAppFn(v_classTy_1460_);
if (lean_obj_tag(v___x_1466_) == 4)
{
lean_object* v_declName_1467_; lean_object* v___x_1468_; 
v_declName_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_declName_1467_);
lean_inc(v_a_1464_);
lean_inc_ref(v_a_1463_);
lean_inc(v_a_1462_);
lean_inc_ref(v_a_1461_);
v___x_1468_ = lean_infer_type(v___x_1466_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___f_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1470_, 0, v_declName_1467_);
v___x_1471_ = 0;
v___x_1472_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1469_, v___f_1470_, v___x_1471_, v___x_1471_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_declName_1467_);
v_a_1473_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1468_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1468_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v___x_1466_);
v___x_1481_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec_ref(v_classTy_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1490_, lean_object* v_as_1491_, lean_object* v_j_1492_){
_start:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_array_get_size(v_as_1491_);
v___x_1494_ = lean_nat_dec_lt(v_j_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v_j_1492_);
v___x_1495_ = lean_box(0);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_array_fget_borrowed(v_as_1491_, v_j_1492_);
v___x_1497_ = l_Lean_Expr_mvarId_x21(v___x_1496_);
v___x_1498_ = l_Lean_instBEqMVarId_beq(v___x_1497_, v_a_1490_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_j_1492_, v___x_1499_);
lean_dec(v_j_1492_);
v_j_1492_ = v___x_1500_;
goto _start;
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_j_1492_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1503_, lean_object* v_as_1504_, lean_object* v_j_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1503_, v_as_1504_, v_j_1505_);
lean_dec_ref(v_as_1504_);
lean_dec(v_a_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
lean_object* v_ks_1511_; lean_object* v_vs_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1536_; 
v_ks_1511_ = lean_ctor_get(v_x_1507_, 0);
v_vs_1512_ = lean_ctor_get(v_x_1507_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1514_ = v_x_1507_;
v_isShared_1515_ = v_isSharedCheck_1536_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_vs_1512_);
lean_inc(v_ks_1511_);
lean_dec(v_x_1507_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1536_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = lean_array_get_size(v_ks_1511_);
v___x_1517_ = lean_nat_dec_lt(v_x_1508_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_dec(v_x_1508_);
v___x_1518_ = lean_array_push(v_ks_1511_, v_x_1509_);
v___x_1519_ = lean_array_push(v_vs_1512_, v_x_1510_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1519_);
lean_ctor_set(v___x_1514_, 0, v___x_1518_);
v___x_1521_ = v___x_1514_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
else
{
lean_object* v_k_x27_1523_; uint8_t v___x_1524_; 
v_k_x27_1523_ = lean_array_fget_borrowed(v_ks_1511_, v_x_1508_);
v___x_1524_ = l_Lean_instBEqMVarId_beq(v_x_1509_, v_k_x27_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1526_; 
if (v_isShared_1515_ == 0)
{
v___x_1526_ = v___x_1514_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_ks_1511_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_vs_1512_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_add(v_x_1508_, v___x_1527_);
lean_dec(v_x_1508_);
v_x_1507_ = v___x_1526_;
v_x_1508_ = v___x_1528_;
goto _start;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = lean_array_fset(v_ks_1511_, v_x_1508_, v_x_1509_);
v___x_1532_ = lean_array_fset(v_vs_1512_, v_x_1508_, v_x_1510_);
lean_dec(v_x_1508_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1532_);
lean_ctor_set(v___x_1514_, 0, v___x_1531_);
v___x_1534_ = v___x_1514_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1532_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1537_, lean_object* v_k_1538_, lean_object* v_v_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1537_, v___x_1540_, v_k_1538_, v_v_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1542_, size_t v_x_1543_, size_t v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v_es_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; lean_object* v_j_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_es_1547_ = lean_ctor_get(v_x_1542_, 0);
v___x_1548_ = ((size_t)5ULL);
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_1551_ = lean_usize_land(v_x_1543_, v___x_1550_);
v_j_1552_ = lean_usize_to_nat(v___x_1551_);
v___x_1553_ = lean_array_get_size(v_es_1547_);
v___x_1554_ = lean_nat_dec_lt(v_j_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_dec(v_j_1552_);
lean_dec(v_x_1546_);
lean_dec(v_x_1545_);
return v_x_1542_;
}
else
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1591_; 
lean_inc_ref(v_es_1547_);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_x_1542_, 0);
lean_dec(v_unused_1592_);
v___x_1556_ = v_x_1542_;
v_isShared_1557_ = v_isSharedCheck_1591_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_x_1542_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1591_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_v_1558_; lean_object* v___x_1559_; lean_object* v_xs_x27_1560_; lean_object* v___y_1562_; 
v_v_1558_ = lean_array_fget(v_es_1547_, v_j_1552_);
v___x_1559_ = lean_box(0);
v_xs_x27_1560_ = lean_array_fset(v_es_1547_, v_j_1552_, v___x_1559_);
switch(lean_obj_tag(v_v_1558_))
{
case 0:
{
lean_object* v_key_1567_; lean_object* v_val_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1578_; 
v_key_1567_ = lean_ctor_get(v_v_1558_, 0);
v_val_1568_ = lean_ctor_get(v_v_1558_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_v_1558_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1570_ = v_v_1558_;
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_val_1568_);
lean_inc(v_key_1567_);
lean_dec(v_v_1558_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
uint8_t v___x_1572_; 
v___x_1572_ = l_Lean_instBEqMVarId_beq(v_x_1545_, v_key_1567_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1570_);
v___x_1573_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1567_, v_val_1568_, v_x_1545_, v_x_1546_);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___y_1562_ = v___x_1574_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1576_; 
lean_dec(v_val_1568_);
lean_dec(v_key_1567_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_x_1546_);
lean_ctor_set(v___x_1570_, 0, v_x_1545_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_x_1545_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_x_1546_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
v___y_1562_ = v___x_1576_;
goto v___jp_1561_;
}
}
}
}
case 1:
{
lean_object* v_node_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1589_; 
v_node_1579_ = lean_ctor_get(v_v_1558_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_v_1558_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1581_ = v_v_1558_;
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_node_1579_);
lean_dec(v_v_1558_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1583_ = lean_usize_shift_right(v_x_1543_, v___x_1548_);
v___x_1584_ = lean_usize_add(v_x_1544_, v___x_1549_);
v___x_1585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1579_, v___x_1583_, v___x_1584_, v_x_1545_, v_x_1546_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v___y_1562_ = v___x_1587_;
goto v___jp_1561_;
}
}
}
default: 
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_x_1545_);
lean_ctor_set(v___x_1590_, 1, v_x_1546_);
v___y_1562_ = v___x_1590_;
goto v___jp_1561_;
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_array_fset(v_xs_x27_1560_, v_j_1552_, v___y_1562_);
lean_dec(v_j_1552_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1563_);
v___x_1565_ = v___x_1556_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_ks_1593_; lean_object* v_vs_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1614_; 
v_ks_1593_ = lean_ctor_get(v_x_1542_, 0);
v_vs_1594_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1596_ = v_x_1542_;
v_isShared_1597_ = v_isSharedCheck_1614_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_vs_1594_);
lean_inc(v_ks_1593_);
lean_dec(v_x_1542_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1614_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_ks_1593_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_vs_1594_);
v___x_1599_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v_newNode_1600_; uint8_t v___y_1602_; size_t v___x_1608_; uint8_t v___x_1609_; 
v_newNode_1600_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1599_, v_x_1545_, v_x_1546_);
v___x_1608_ = ((size_t)7ULL);
v___x_1609_ = lean_usize_dec_le(v___x_1608_, v_x_1544_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1600_);
v___x_1611_ = lean_unsigned_to_nat(4u);
v___x_1612_ = lean_nat_dec_lt(v___x_1610_, v___x_1611_);
lean_dec(v___x_1610_);
v___y_1602_ = v___x_1612_;
goto v___jp_1601_;
}
else
{
v___y_1602_ = v___x_1609_;
goto v___jp_1601_;
}
v___jp_1601_:
{
if (v___y_1602_ == 0)
{
lean_object* v_ks_1603_; lean_object* v_vs_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_ks_1603_ = lean_ctor_get(v_newNode_1600_, 0);
lean_inc_ref(v_ks_1603_);
v_vs_1604_ = lean_ctor_get(v_newNode_1600_, 1);
lean_inc_ref(v_vs_1604_);
lean_dec_ref(v_newNode_1600_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_1607_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1544_, v_ks_1603_, v_vs_1604_, v___x_1605_, v___x_1606_);
lean_dec_ref(v_vs_1604_);
lean_dec_ref(v_ks_1603_);
return v___x_1607_;
}
else
{
return v_newNode_1600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1615_, lean_object* v_keys_1616_, lean_object* v_vals_1617_, lean_object* v_i_1618_, lean_object* v_entries_1619_){
_start:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_array_get_size(v_keys_1616_);
v___x_1621_ = lean_nat_dec_lt(v_i_1618_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec(v_i_1618_);
return v_entries_1619_;
}
else
{
lean_object* v_k_1622_; lean_object* v_v_1623_; uint64_t v___x_1624_; size_t v_h_1625_; size_t v___x_1626_; lean_object* v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; size_t v_h_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_k_1622_ = lean_array_fget_borrowed(v_keys_1616_, v_i_1618_);
v_v_1623_ = lean_array_fget_borrowed(v_vals_1617_, v_i_1618_);
v___x_1624_ = l_Lean_instHashableMVarId_hash(v_k_1622_);
v_h_1625_ = lean_uint64_to_usize(v___x_1624_);
v___x_1626_ = ((size_t)5ULL);
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_sub(v_depth_1615_, v___x_1628_);
v___x_1630_ = lean_usize_mul(v___x_1626_, v___x_1629_);
v_h_1631_ = lean_usize_shift_right(v_h_1625_, v___x_1630_);
v___x_1632_ = lean_nat_add(v_i_1618_, v___x_1627_);
lean_dec(v_i_1618_);
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
v___x_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1619_, v_h_1631_, v_depth_1615_, v_k_1622_, v_v_1623_);
v_i_1618_ = v___x_1632_;
v_entries_1619_ = v___x_1633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1635_, lean_object* v_keys_1636_, lean_object* v_vals_1637_, lean_object* v_i_1638_, lean_object* v_entries_1639_){
_start:
{
size_t v_depth_boxed_1640_; lean_object* v_res_1641_; 
v_depth_boxed_1640_ = lean_unbox_usize(v_depth_1635_);
lean_dec(v_depth_1635_);
v_res_1641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1640_, v_keys_1636_, v_vals_1637_, v_i_1638_, v_entries_1639_);
lean_dec_ref(v_vals_1637_);
lean_dec_ref(v_keys_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
size_t v_x_1628__boxed_1647_; size_t v_x_1629__boxed_1648_; lean_object* v_res_1649_; 
v_x_1628__boxed_1647_ = lean_unbox_usize(v_x_1643_);
lean_dec(v_x_1643_);
v_x_1629__boxed_1648_ = lean_unbox_usize(v_x_1644_);
lean_dec(v_x_1644_);
v_res_1649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1642_, v_x_1628__boxed_1647_, v_x_1629__boxed_1648_, v_x_1645_, v_x_1646_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
uint64_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1653_ = l_Lean_instHashableMVarId_hash(v_x_1651_);
v___x_1654_ = lean_uint64_to_usize(v___x_1653_);
v___x_1655_ = ((size_t)1ULL);
v___x_1656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1650_, v___x_1654_, v___x_1655_, v_x_1651_, v_x_1652_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1657_, lean_object* v_val_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v_mctx_1662_; lean_object* v_cache_1663_; lean_object* v_zetaDeltaFVarIds_1664_; lean_object* v_postponed_1665_; lean_object* v_diag_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1694_; 
v___x_1661_ = lean_st_ref_take(v___y_1659_);
v_mctx_1662_ = lean_ctor_get(v___x_1661_, 0);
v_cache_1663_ = lean_ctor_get(v___x_1661_, 1);
v_zetaDeltaFVarIds_1664_ = lean_ctor_get(v___x_1661_, 2);
v_postponed_1665_ = lean_ctor_get(v___x_1661_, 3);
v_diag_1666_ = lean_ctor_get(v___x_1661_, 4);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1668_ = v___x_1661_;
v_isShared_1669_ = v_isSharedCheck_1694_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_diag_1666_);
lean_inc(v_postponed_1665_);
lean_inc(v_zetaDeltaFVarIds_1664_);
lean_inc(v_cache_1663_);
lean_inc(v_mctx_1662_);
lean_dec(v___x_1661_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1694_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_depth_1670_; lean_object* v_levelAssignDepth_1671_; lean_object* v_lmvarCounter_1672_; lean_object* v_mvarCounter_1673_; lean_object* v_lDecls_1674_; lean_object* v_decls_1675_; lean_object* v_userNames_1676_; lean_object* v_lAssignment_1677_; lean_object* v_eAssignment_1678_; lean_object* v_dAssignment_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1693_; 
v_depth_1670_ = lean_ctor_get(v_mctx_1662_, 0);
v_levelAssignDepth_1671_ = lean_ctor_get(v_mctx_1662_, 1);
v_lmvarCounter_1672_ = lean_ctor_get(v_mctx_1662_, 2);
v_mvarCounter_1673_ = lean_ctor_get(v_mctx_1662_, 3);
v_lDecls_1674_ = lean_ctor_get(v_mctx_1662_, 4);
v_decls_1675_ = lean_ctor_get(v_mctx_1662_, 5);
v_userNames_1676_ = lean_ctor_get(v_mctx_1662_, 6);
v_lAssignment_1677_ = lean_ctor_get(v_mctx_1662_, 7);
v_eAssignment_1678_ = lean_ctor_get(v_mctx_1662_, 8);
v_dAssignment_1679_ = lean_ctor_get(v_mctx_1662_, 9);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_mctx_1662_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1681_ = v_mctx_1662_;
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_dAssignment_1679_);
lean_inc(v_eAssignment_1678_);
lean_inc(v_lAssignment_1677_);
lean_inc(v_userNames_1676_);
lean_inc(v_decls_1675_);
lean_inc(v_lDecls_1674_);
lean_inc(v_mvarCounter_1673_);
lean_inc(v_lmvarCounter_1672_);
lean_inc(v_levelAssignDepth_1671_);
lean_inc(v_depth_1670_);
lean_dec(v_mctx_1662_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1678_, v_mvarId_1657_, v_val_1658_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 8, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_depth_1670_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_levelAssignDepth_1671_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_lmvarCounter_1672_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_mvarCounter_1673_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v_lDecls_1674_);
lean_ctor_set(v_reuseFailAlloc_1692_, 5, v_decls_1675_);
lean_ctor_set(v_reuseFailAlloc_1692_, 6, v_userNames_1676_);
lean_ctor_set(v_reuseFailAlloc_1692_, 7, v_lAssignment_1677_);
lean_ctor_set(v_reuseFailAlloc_1692_, 8, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1692_, 9, v_dAssignment_1679_);
v___x_1685_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1685_);
v___x_1687_ = v___x_1668_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_zetaDeltaFVarIds_1664_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_postponed_1665_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_diag_1666_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_st_ref_set(v___y_1659_, v___x_1687_);
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1695_, lean_object* v_val_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1695_, v_val_1696_, v___y_1697_);
lean_dec(v___y_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1700_, lean_object* v_argVars_1701_, lean_object* v_as_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_b_1705_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v_a_1714_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1713_ = lean_box(0);
v_a_1714_ = lean_array_uget_borrowed(v_as_1702_, v_i_1704_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1714_, v_argMVars_1700_, v___x_1735_);
if (lean_obj_tag(v___x_1736_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_val_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l_Lean_instInhabitedExpr;
v___x_1739_ = lean_array_get_borrowed(v___x_1738_, v_argVars_1701_, v_val_1737_);
lean_dec(v_val_1737_);
lean_inc(v___x_1739_);
lean_inc(v_a_1714_);
v___x_1740_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1714_, v___x_1739_, v___y_1707_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_dec_ref(v___x_1740_);
v___y_1716_ = v___y_1706_;
v___y_1717_ = v___y_1707_;
v___y_1718_ = v___y_1708_;
v___y_1719_ = v___y_1709_;
goto v___jp_1715_;
}
else
{
return v___x_1740_;
}
}
else
{
lean_dec(v___x_1736_);
v___y_1716_ = v___y_1706_;
v___y_1717_ = v___y_1707_;
v___y_1718_ = v___y_1708_;
v___y_1719_ = v___y_1709_;
goto v___jp_1715_;
}
v___jp_1715_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_inc(v_a_1714_);
v___x_1720_ = l_Lean_Expr_mvar___override(v_a_1714_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
v___x_1721_ = lean_infer_type(v___x_1720_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1700_, v_argVars_1701_, v_a_1722_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1723_) == 0)
{
size_t v___x_1724_; size_t v___x_1725_; 
lean_dec_ref(v___x_1723_);
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1704_, v___x_1724_);
v_i_1704_ = v___x_1725_;
v_b_1705_ = v___x_1713_;
goto _start;
}
else
{
return v___x_1723_;
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1727_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1721_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1721_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1741_, lean_object* v_argVars_1742_, lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_getMVars(v_e_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; size_t v_sz_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_box(0);
v_sz_1752_ = lean_array_size(v_a_1750_);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1741_, v_argVars_1742_, v_a_1750_, v_sz_1752_, v___x_1753_, v___x_1751_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1750_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1754_, 0);
lean_dec(v_unused_1762_);
v___x_1756_ = v___x_1754_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v___x_1754_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1751_);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1751_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
return v___x_1754_;
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1749_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1749_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1771_, lean_object* v_argVars_1772_, lean_object* v_e_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1771_, v_argVars_1772_, v_e_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v_argVars_1772_);
lean_dec_ref(v_argMVars_1771_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1780_, lean_object* v_argVars_1781_, lean_object* v_as_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1780_, v_argVars_1781_, v_as_1782_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_as_1782_);
lean_dec_ref(v_argVars_1781_);
lean_dec_ref(v_argMVars_1780_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1794_, lean_object* v_val_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1794_, v_val_1795_, v___y_1797_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1802_, lean_object* v_val_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1802_, v_val_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1811_, v_x_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1815_, lean_object* v_x_1816_, size_t v_x_1817_, size_t v_x_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1816_, v_x_1817_, v_x_1818_, v_x_1819_, v_x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
size_t v_x_1991__boxed_1828_; size_t v_x_1992__boxed_1829_; lean_object* v_res_1830_; 
v_x_1991__boxed_1828_ = lean_unbox_usize(v_x_1824_);
lean_dec(v_x_1824_);
v_x_1992__boxed_1829_ = lean_unbox_usize(v_x_1825_);
lean_dec(v_x_1825_);
v_res_1830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1822_, v_x_1823_, v_x_1991__boxed_1828_, v_x_1992__boxed_1829_, v_x_1826_, v_x_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1831_, lean_object* v_n_1832_, lean_object* v_k_1833_, lean_object* v_v_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1832_, v_k_1833_, v_v_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1836_, size_t v_depth_1837_, lean_object* v_keys_1838_, lean_object* v_vals_1839_, lean_object* v_heq_1840_, lean_object* v_i_1841_, lean_object* v_entries_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1837_, v_keys_1838_, v_vals_1839_, v_i_1841_, v_entries_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_depth_1845_, lean_object* v_keys_1846_, lean_object* v_vals_1847_, lean_object* v_heq_1848_, lean_object* v_i_1849_, lean_object* v_entries_1850_){
_start:
{
size_t v_depth_boxed_1851_; lean_object* v_res_1852_; 
v_depth_boxed_1851_ = lean_unbox_usize(v_depth_1845_);
lean_dec(v_depth_1845_);
v_res_1852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1844_, v_depth_boxed_1851_, v_keys_1846_, v_vals_1847_, v_heq_1848_, v_i_1849_, v_entries_1850_);
lean_dec_ref(v_vals_1847_);
lean_dec_ref(v_keys_1846_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1854_, v_x_1855_, v_x_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1859_, lean_object* v___y_1860_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_Expr_hasMVar(v_e_1859_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_e_1859_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v_mctx_1865_; lean_object* v___x_1866_; lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; lean_object* v_cache_1870_; lean_object* v_zetaDeltaFVarIds_1871_; lean_object* v_postponed_1872_; lean_object* v_diag_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
v___x_1864_ = lean_st_ref_get(v___y_1860_);
v_mctx_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc_ref(v_mctx_1865_);
lean_dec(v___x_1864_);
v___x_1866_ = l_Lean_instantiateMVarsCore(v_mctx_1865_, v_e_1859_);
v_fst_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_fst_1867_);
v_snd_1868_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_snd_1868_);
lean_dec_ref(v___x_1866_);
v___x_1869_ = lean_st_ref_take(v___y_1860_);
v_cache_1870_ = lean_ctor_get(v___x_1869_, 1);
v_zetaDeltaFVarIds_1871_ = lean_ctor_get(v___x_1869_, 2);
v_postponed_1872_ = lean_ctor_get(v___x_1869_, 3);
v_diag_1873_ = lean_ctor_get(v___x_1869_, 4);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1883_);
v___x_1875_ = v___x_1869_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_diag_1873_);
lean_inc(v_postponed_1872_);
lean_inc(v_zetaDeltaFVarIds_1871_);
lean_inc(v_cache_1870_);
lean_dec(v___x_1869_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_snd_1868_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_snd_1868_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_zetaDeltaFVarIds_1871_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_postponed_1872_);
lean_ctor_set(v_reuseFailAlloc_1881_, 4, v_diag_1873_);
v___x_1878_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_st_ref_set(v___y_1860_, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_fst_1867_);
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1884_, v___y_1885_);
lean_dec(v___y_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1888_, v___y_1890_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1902_, lean_object* v_opt_1903_){
_start:
{
lean_object* v_name_1904_; lean_object* v_defValue_1905_; lean_object* v_map_1906_; lean_object* v___x_1907_; 
v_name_1904_ = lean_ctor_get(v_opt_1903_, 0);
v_defValue_1905_ = lean_ctor_get(v_opt_1903_, 1);
v_map_1906_ = lean_ctor_get(v_opts_1902_, 0);
v___x_1907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1906_, v_name_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_unbox(v_defValue_1905_);
return v___x_1908_;
}
else
{
lean_object* v_val_1909_; 
v_val_1909_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1909_);
lean_dec_ref(v___x_1907_);
if (lean_obj_tag(v_val_1909_) == 1)
{
uint8_t v_v_1910_; 
v_v_1910_ = lean_ctor_get_uint8(v_val_1909_, 0);
lean_dec_ref(v_val_1909_);
return v_v_1910_;
}
else
{
uint8_t v___x_1911_; 
lean_dec(v_val_1909_);
v___x_1911_ = lean_unbox(v_defValue_1905_);
return v___x_1911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1912_, lean_object* v_opt_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1912_, v_opt_1913_);
lean_dec_ref(v_opt_1913_);
lean_dec_ref(v_opts_1912_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1916_, lean_object* v_as_1917_, size_t v_i_1918_, size_t v_stop_1919_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_usize_dec_eq(v_i_1918_, v_stop_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_array_uget_borrowed(v_as_1917_, v_i_1918_);
v___x_1922_ = lean_nat_dec_eq(v_a_1916_, v___x_1921_);
if (v___x_1922_ == 0)
{
size_t v___x_1923_; size_t v___x_1924_; 
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1918_, v___x_1923_);
v_i_1918_ = v___x_1924_;
goto _start;
}
else
{
return v___x_1922_;
}
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1927_, lean_object* v_as_1928_, lean_object* v_i_1929_, lean_object* v_stop_1930_){
_start:
{
size_t v_i_boxed_1931_; size_t v_stop_boxed_1932_; uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_i_boxed_1931_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_stop_boxed_1932_ = lean_unbox_usize(v_stop_1930_);
lean_dec(v_stop_1930_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1927_, v_as_1928_, v_i_boxed_1931_, v_stop_boxed_1932_);
lean_dec_ref(v_as_1928_);
lean_dec(v_a_1927_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_array_get_size(v_as_1935_);
v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
return v___x_1939_;
}
else
{
if (v___x_1939_ == 0)
{
return v___x_1939_;
}
else
{
size_t v___x_1940_; size_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_of_nat(v___x_1938_);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1936_, v_as_1935_, v___x_1940_, v___x_1941_);
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1943_, lean_object* v_a_1944_){
_start:
{
uint8_t v_res_1945_; lean_object* v_r_1946_; 
v_res_1945_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_as_1943_);
v_r_1946_ = lean_box(v_res_1945_);
return v_r_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1947_, lean_object* v_fst_1948_, lean_object* v_argVars_1949_, lean_object* v_as_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_a_1960_; uint8_t v___x_1964_; 
v___x_1964_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1953_);
return v___x_1965_;
}
else
{
lean_object* v_next_1966_; 
v_next_1966_ = lean_ctor_get(v_b_1953_, 0);
lean_inc(v_next_1966_);
if (lean_obj_tag(v_next_1966_) == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1953_);
return v___x_1967_;
}
else
{
lean_object* v_upperBound_1968_; lean_object* v_val_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2000_; 
v_upperBound_1968_ = lean_ctor_get(v_b_1953_, 1);
v_val_1969_ = lean_ctor_get(v_next_1966_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_next_1966_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1971_ = v_next_1966_;
v_isShared_1972_ = v_isSharedCheck_2000_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_val_1969_);
lean_dec(v_next_1966_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2000_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_nat_dec_lt(v_val_1969_, v_upperBound_1968_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_b_1953_);
return v___x_1974_;
}
else
{
lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1997_; 
lean_inc(v_upperBound_1968_);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_b_1953_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1998_ = lean_ctor_get(v_b_1953_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_b_1953_, 0);
lean_dec(v_unused_1999_);
v___x_1976_ = v_b_1953_;
v_isShared_1977_ = v_isSharedCheck_1997_;
goto v_resetjp_1975_;
}
else
{
lean_dec(v_b_1953_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1997_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_val_1969_, v___x_1978_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1979_);
v___x_1981_ = v___x_1971_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1981_);
v___x_1983_ = v___x_1976_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_upperBound_1968_);
v___x_1983_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1947_, v_val_1969_);
lean_dec(v_val_1969_);
if (v___x_1984_ == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; 
v_a_1985_ = lean_array_uget_borrowed(v_as_1950_, v_i_1952_);
lean_inc(v_a_1985_);
v___x_1986_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1948_, v_argVars_1949_, v_a_1985_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_dec_ref(v___x_1986_);
v_a_1960_ = v___x_1983_;
goto v___jp_1959_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v___x_1983_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
v_a_1960_ = v___x_1983_;
goto v___jp_1959_;
}
}
}
}
}
}
}
}
v___jp_1959_:
{
size_t v___x_1961_; size_t v___x_1962_; 
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_add(v_i_1952_, v___x_1961_);
v_i_1952_ = v___x_1962_;
v_b_1953_ = v_a_1960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2001_, lean_object* v_fst_2002_, lean_object* v_argVars_2003_, lean_object* v_as_2004_, lean_object* v_sz_2005_, lean_object* v_i_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
size_t v_sz_boxed_2013_; size_t v_i_boxed_2014_; lean_object* v_res_2015_; 
v_sz_boxed_2013_ = lean_unbox_usize(v_sz_2005_);
lean_dec(v_sz_2005_);
v_i_boxed_2014_ = lean_unbox_usize(v_i_2006_);
lean_dec(v_i_2006_);
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2001_, v_fst_2002_, v_argVars_2003_, v_as_2004_, v_sz_boxed_2013_, v_i_boxed_2014_, v_b_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec_ref(v_as_2004_);
lean_dec_ref(v_argVars_2003_);
lean_dec_ref(v_fst_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
if (lean_obj_tag(v_a_2017_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_List_reverse___redArg(v_a_2018_);
return v___x_2019_;
}
else
{
lean_object* v_head_2020_; lean_object* v_tail_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2036_; 
v_head_2020_ = lean_ctor_get(v_a_2017_, 0);
v_tail_2021_ = lean_ctor_get(v_a_2017_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2023_ = v_a_2017_;
v_isShared_2024_ = v_isSharedCheck_2036_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_tail_2021_);
lean_inc(v_head_2020_);
lean_dec(v_a_2017_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2036_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2025_ = 0;
v___x_2026_ = lean_box(v___x_2025_);
v___x_2027_ = lean_array_get(v___x_2026_, v_fst_2016_, v_head_2020_);
lean_dec(v___x_2026_);
v___x_2028_ = 3;
v___x_2029_ = lean_unbox(v___x_2027_);
lean_dec(v___x_2027_);
v___x_2030_ = l_Lean_instBEqBinderInfo_beq(v___x_2029_, v___x_2028_);
if (v___x_2030_ == 0)
{
lean_del_object(v___x_2023_);
lean_dec(v_head_2020_);
v_a_2017_ = v_tail_2021_;
goto _start;
}
else
{
lean_object* v___x_2033_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v_a_2018_);
v___x_2033_ = v___x_2023_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_head_2020_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2018_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v_a_2017_ = v_tail_2021_;
v_a_2018_ = v___x_2033_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2037_, v_a_2038_, v_a_2039_);
lean_dec_ref(v_fst_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2041_, lean_object* v___x_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_b_2045_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_lt(v_a_2044_, v_upperBound_2041_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v_a_2044_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2045_);
return v___x_2048_;
}
else
{
lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2090_; 
v_snd_2049_ = lean_ctor_get(v_b_2045_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_b_2045_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v_b_2045_, 0);
lean_dec(v_unused_2091_);
v___x_2051_ = v_b_2045_;
v_isShared_2052_ = v_isSharedCheck_2090_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_dec(v_b_2045_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2090_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_array_2053_; lean_object* v_start_2054_; lean_object* v_stop_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_array_2053_ = lean_ctor_get(v_snd_2049_, 0);
v_start_2054_ = lean_ctor_get(v_snd_2049_, 1);
v_stop_2055_ = lean_ctor_get(v_snd_2049_, 2);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_nat_dec_lt(v_start_2054_, v_stop_2055_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2059_; 
lean_dec(v_a_2044_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2056_);
v___x_2059_ = v___x_2051_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_snd_2049_);
v___x_2059_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
else
{
lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2086_; 
lean_inc(v_stop_2055_);
lean_inc(v_start_2054_);
lean_inc_ref(v_array_2053_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_snd_2049_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2087_ = lean_ctor_get(v_snd_2049_, 2);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_snd_2049_, 1);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_snd_2049_, 0);
lean_dec(v_unused_2089_);
v___x_2063_ = v_snd_2049_;
v_isShared_2064_ = v_isSharedCheck_2086_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v_snd_2049_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2086_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_nat_dec_eq(v___x_2042_, v___x_2065_);
v___x_2067_ = lean_array_fget(v_array_2053_, v_start_2054_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_start_2054_, v___x_2068_);
lean_dec(v_start_2054_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2069_);
v___x_2071_ = v___x_2063_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_array_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_stop_2055_);
v___x_2071_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2043_, v_a_2044_);
if (v___x_2084_ == 0)
{
goto v___jp_2078_;
}
else
{
if (v___x_2066_ == 0)
{
lean_dec(v___x_2067_);
goto v___jp_2072_;
}
else
{
goto v___jp_2078_;
}
}
v___jp_2072_:
{
lean_object* v___x_2074_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2071_);
lean_ctor_set(v___x_2051_, 0, v___x_2056_);
v___x_2074_ = v___x_2051_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2071_);
v___x_2074_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_nat_add(v_a_2044_, v___x_2068_);
lean_dec(v_a_2044_);
v_a_2044_ = v___x_2075_;
v_b_2045_ = v___x_2074_;
goto _start;
}
}
v___jp_2078_:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Lean_Expr_hasExprMVar(v___x_2067_);
lean_dec(v___x_2067_);
if (v___x_2079_ == 0)
{
goto v___jp_2072_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_del_object(v___x_2051_);
lean_dec(v_a_2044_);
v___x_2080_ = lean_box(v___x_2066_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2071_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2092_, lean_object* v___x_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2092_, v___x_2093_, v_a_2094_, v_a_2095_, v_b_2096_);
lean_dec_ref(v_a_2094_);
lean_dec(v___x_2093_);
lean_dec(v_upperBound_2092_);
return v_res_2098_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2099_; lean_object* v_dummy_2100_; 
v___x_2099_ = lean_box(0);
v_dummy_2100_ = l_Lean_Expr_sort___override(v___x_2099_);
return v_dummy_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2101_, lean_object* v___x_2102_, uint8_t v___x_2103_, lean_object* v_x_2104_, lean_object* v_argTy_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
v___x_2111_ = lean_whnf(v_argTy_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2112_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v_dummy_2115_; lean_object* v_nargs_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2113_);
v_dummy_2115_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2116_ = l_Lean_Expr_getAppNumArgs(v_a_2112_);
lean_inc(v_nargs_2116_);
v___x_2117_ = lean_mk_array(v_nargs_2116_, v_dummy_2115_);
v___x_2118_ = lean_unsigned_to_nat(1u);
v___x_2119_ = lean_nat_sub(v_nargs_2116_, v___x_2118_);
lean_dec(v_nargs_2116_);
v___x_2120_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2112_, v___x_2117_, v___x_2119_);
v___x_2121_ = lean_array_get_size(v___x_2120_);
lean_inc(v___x_2101_);
v___x_2122_ = l_Array_toSubarray___redArg(v___x_2120_, v___x_2101_, v___x_2121_);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
v___x_2125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2121_, v___x_2102_, v_a_2114_, v___x_2101_, v___x_2124_);
lean_dec(v_a_2114_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2139_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_fst_2130_; 
v_fst_2130_ = lean_ctor_get(v_a_2126_, 0);
lean_inc(v_fst_2130_);
lean_dec(v_a_2126_);
if (lean_obj_tag(v_fst_2130_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_box(v___x_2103_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
else
{
lean_object* v_val_2135_; lean_object* v___x_2137_; 
v_val_2135_ = lean_ctor_get(v_fst_2130_, 0);
lean_inc(v_val_2135_);
lean_dec_ref(v_fst_2130_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_val_2135_);
v___x_2137_ = v___x_2128_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_val_2135_);
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
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2125_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2125_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2112_);
lean_dec(v___x_2101_);
v_a_2148_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2113_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2113_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v___x_2101_);
v_a_2156_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2111_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2111_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2164_, lean_object* v___x_2165_, lean_object* v___x_2166_, lean_object* v_x_2167_, lean_object* v_argTy_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___x_24490__boxed_2174_; lean_object* v_res_2175_; 
v___x_24490__boxed_2174_ = lean_unbox(v___x_2166_);
v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2164_, v___x_2165_, v___x_24490__boxed_2174_, v_x_2167_, v_argTy_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec_ref(v_x_2167_);
lean_dec(v___x_2165_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2179_, lean_object* v_projInfo_x3f_2180_, lean_object* v___x_2181_, lean_object* v_argVars_2182_, lean_object* v_as_2183_, size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec(v___x_2181_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_b_2186_);
return v___x_2193_;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_b_2186_);
v_a_2194_ = lean_array_uget_borrowed(v_as_2183_, v_i_2185_);
v___x_2195_ = l_Lean_instInhabitedExpr;
v___x_2196_ = lean_array_get_borrowed(v___x_2195_, v_fst_2179_, v_a_2194_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc(v___x_2196_);
v___x_2197_ = lean_infer_type(v___x_2196_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2198_, v___y_2188_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2246_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2246_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2246_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2212_; lean_object* v___y_2214_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___f_2230_; uint8_t v___x_2231_; 
v___x_2204_ = lean_box(0);
v___x_2212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_box(v___x_2192_);
lean_inc(v___x_2181_);
v___f_2230_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2230_, 0, v___x_2228_);
lean_closure_set(v___f_2230_, 1, v___x_2181_);
lean_closure_set(v___f_2230_, 2, v___x_2229_);
v___x_2231_ = lean_nat_dec_eq(v___x_2181_, v___x_2228_);
if (lean_obj_tag(v_projInfo_x3f_2180_) == 1)
{
lean_object* v_val_2232_; lean_object* v_numParams_2233_; uint8_t v___x_2234_; 
v_val_2232_ = lean_ctor_get(v_projInfo_x3f_2180_, 0);
v_numParams_2233_ = lean_ctor_get(v_val_2232_, 1);
v___x_2234_ = lean_nat_dec_eq(v_numParams_2233_, v_a_2194_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2200_, v___f_2230_, v___x_2231_, v___x_2231_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
v___y_2214_ = v___x_2235_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2236_; 
lean_dec_ref(v___f_2230_);
lean_dec(v___x_2181_);
v___x_2236_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2179_, v_argVars_2182_, v_a_2200_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_dec_ref(v___x_2236_);
goto v___jp_2205_;
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_2202_);
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2200_, v___f_2230_, v___x_2231_, v___x_2231_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
v___y_2214_ = v___x_2245_;
goto v___jp_2213_;
}
v___jp_2205_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_inc(v_a_2194_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2194_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2204_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2208_);
v___x_2210_ = v___x_2202_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
v___jp_2213_:
{
if (lean_obj_tag(v___y_2214_) == 0)
{
lean_object* v_a_2215_; uint8_t v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___y_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___y_2214_);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2216_ == 0)
{
size_t v___x_2217_; size_t v___x_2218_; 
lean_del_object(v___x_2202_);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2185_, v___x_2217_);
v_i_2185_ = v___x_2218_;
v_b_2186_ = v___x_2212_;
goto _start;
}
else
{
lean_dec(v___x_2181_);
goto v___jp_2205_;
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2202_);
lean_dec(v___x_2181_);
v_a_2220_ = lean_ctor_get(v___y_2214_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___y_2214_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___y_2214_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___y_2214_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___x_2181_);
v_a_2247_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2199_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2199_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2181_);
v_a_2255_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2197_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2197_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2263_, lean_object* v_projInfo_x3f_2264_, lean_object* v___x_2265_, lean_object* v_argVars_2266_, lean_object* v_as_2267_, lean_object* v_sz_2268_, lean_object* v_i_2269_, lean_object* v_b_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2268_);
lean_dec(v_sz_2268_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2263_, v_projInfo_x3f_2264_, v___x_2265_, v_argVars_2266_, v_as_2267_, v_sz_boxed_2276_, v_i_boxed_2277_, v_b_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_as_2267_);
lean_dec_ref(v_argVars_2266_);
lean_dec(v_projInfo_x3f_2264_);
lean_dec_ref(v_fst_2263_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v_env_2286_; lean_object* v___x_2287_; lean_object* v_mctx_2288_; lean_object* v_lctx_2289_; lean_object* v_options_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2285_ = lean_st_ref_get(v___y_2283_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_env_2286_);
lean_dec(v___x_2285_);
v___x_2287_ = lean_st_ref_get(v___y_2281_);
v_mctx_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_ref(v_mctx_2288_);
lean_dec(v___x_2287_);
v_lctx_2289_ = lean_ctor_get(v___y_2280_, 2);
v_options_2290_ = lean_ctor_get(v___y_2282_, 2);
lean_inc_ref(v_options_2290_);
lean_inc_ref(v_lctx_2289_);
v___x_2291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2291_, 0, v_env_2286_);
lean_ctor_set(v___x_2291_, 1, v_mctx_2288_);
lean_ctor_set(v___x_2291_, 2, v_lctx_2289_);
lean_ctor_set(v___x_2291_, 3, v_options_2290_);
v___x_2292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v_msgData_2279_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_ref_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2317_; 
v_ref_2307_ = lean_ctor_get(v___y_2304_, 5);
v___x_2308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_inc(v_ref_2307_);
v___x_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2313_, 0, v_ref_2307_);
lean_ctor_set(v___x_2313_, 1, v_a_2309_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 1);
lean_ctor_set(v___x_2311_, 0, v___x_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2325_, lean_object* v_as_2326_, size_t v_i_2327_, size_t v_stop_2328_, lean_object* v_b_2329_){
_start:
{
lean_object* v___y_2331_; uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_eq(v_i_2327_, v_stop_2328_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = lean_array_uget_borrowed(v_as_2326_, v_i_2327_);
v___x_2337_ = lean_nat_dec_eq(v___x_2336_, v_next_2325_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_inc(v___x_2336_);
v___x_2338_ = lean_array_push(v_b_2329_, v___x_2336_);
v___y_2331_ = v___x_2338_;
goto v___jp_2330_;
}
else
{
v___y_2331_ = v_b_2329_;
goto v___jp_2330_;
}
}
else
{
return v_b_2329_;
}
v___jp_2330_:
{
size_t v___x_2332_; size_t v___x_2333_; 
v___x_2332_ = ((size_t)1ULL);
v___x_2333_ = lean_usize_add(v_i_2327_, v___x_2332_);
v_i_2327_ = v___x_2333_;
v_b_2329_ = v___y_2331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2339_, lean_object* v_as_2340_, lean_object* v_i_2341_, lean_object* v_stop_2342_, lean_object* v_b_2343_){
_start:
{
size_t v_i_boxed_2344_; size_t v_stop_boxed_2345_; lean_object* v_res_2346_; 
v_i_boxed_2344_ = lean_unbox_usize(v_i_2341_);
lean_dec(v_i_2341_);
v_stop_boxed_2345_ = lean_unbox_usize(v_stop_2342_);
lean_dec(v_stop_2342_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2339_, v_as_2340_, v_i_boxed_2344_, v_stop_boxed_2345_, v_b_2343_);
lean_dec_ref(v_as_2340_);
lean_dec(v_next_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2347_, size_t v_sz_2348_, size_t v_i_2349_, lean_object* v_bs_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_usize_dec_lt(v_i_2349_, v_sz_2348_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_bs_2350_);
return v___x_2357_;
}
else
{
lean_object* v_v_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_v_2358_ = lean_array_uget_borrowed(v_bs_2350_, v_i_2349_);
v___x_2359_ = l_Lean_instInhabitedExpr;
v___x_2360_ = lean_array_get_borrowed(v___x_2359_, v_fst_2347_, v_v_2358_);
lean_inc(v___y_2354_);
lean_inc_ref(v___y_2353_);
lean_inc(v___y_2352_);
lean_inc_ref(v___y_2351_);
lean_inc(v___x_2360_);
v___x_2361_ = lean_infer_type(v___x_2360_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2362_, v___y_2352_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v_bs_x27_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = lean_unsigned_to_nat(0u);
v_bs_x27_2366_ = lean_array_uset(v_bs_2350_, v_i_2349_, v___x_2365_);
v___x_2367_ = l_Lean_Expr_setPPExplicit(v_a_2364_, v___x_2356_);
v___x_2368_ = l_Lean_indentExpr(v___x_2367_);
v___x_2369_ = ((size_t)1ULL);
v___x_2370_ = lean_usize_add(v_i_2349_, v___x_2369_);
v___x_2371_ = lean_array_uset(v_bs_x27_2366_, v_i_2349_, v___x_2368_);
v_i_2349_ = v___x_2370_;
v_bs_2350_ = v___x_2371_;
goto _start;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v_bs_2350_);
v_a_2373_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2363_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2363_);
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
lean_dec_ref(v_bs_2350_);
v_a_2381_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2361_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2361_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_bs_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
size_t v_sz_boxed_2398_; size_t v_i_boxed_2399_; lean_object* v_res_2400_; 
v_sz_boxed_2398_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2399_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2389_, v_sz_boxed_2398_, v_i_boxed_2399_, v_bs_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v_fst_2389_);
return v_res_2400_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2405_ = l_Lean_MessageData_ofFormat(v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2415_, lean_object* v_argVars_2416_, lean_object* v_inst_2417_, lean_object* v_a_2418_, lean_object* v_projInfo_x3f_2419_, lean_object* v_b_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2557_; 
v_fst_2466_ = lean_ctor_get(v_b_2420_, 0);
v_snd_2467_ = lean_ctor_get(v_b_2420_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_b_2420_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2469_ = v_b_2420_;
v_isShared_2470_ = v_isSharedCheck_2557_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snd_2467_);
lean_inc(v_fst_2466_);
lean_dec(v_b_2420_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2557_;
goto v_resetjp_2468_;
}
v___jp_2426_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = l_Lean_instInhabitedExpr;
v___x_2435_ = lean_array_get_borrowed(v___x_2434_, v_fst_2415_, v___y_2431_);
lean_dec(v___y_2431_);
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2432_);
lean_inc(v___x_2435_);
v___x_2436_ = lean_infer_type(v___x_2435_, v___y_2432_, v___y_2428_, v___y_2429_, v___y_2427_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2415_, v_argVars_2416_, v_a_2437_, v___y_2432_, v___y_2428_, v___y_2429_, v___y_2427_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref(v___x_2438_);
lean_inc(v___x_2435_);
v___x_2439_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2415_, v_argVars_2416_, v___x_2435_, v___y_2432_, v___y_2428_, v___y_2429_, v___y_2427_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2440_; 
lean_dec_ref(v___x_2439_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___y_2430_);
lean_ctor_set(v___x_2440_, 1, v___y_2433_);
v_b_2420_ = v___x_2440_;
goto _start;
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v___y_2433_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2442_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2439_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2439_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___y_2433_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2450_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2438_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2438_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v___y_2433_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2458_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2436_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2436_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
v_resetjp_2468_:
{
lean_object* v_next_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_array_get_size(v_snd_2467_);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = lean_nat_dec_eq(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; size_t v_sz_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
lean_del_object(v___x_2469_);
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2538_ = lean_array_size(v_snd_2467_);
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2415_, v_projInfo_x3f_2419_, v___x_2534_, v_argVars_2416_, v_snd_2467_, v_sz_2538_, v___x_2539_, v___x_2537_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v_fst_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
v_fst_2542_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_fst_2542_);
lean_dec(v_a_2541_);
if (lean_obj_tag(v_fst_2542_) == 0)
{
goto v___jp_2496_;
}
else
{
lean_object* v_val_2543_; 
v_val_2543_ = lean_ctor_get(v_fst_2542_, 0);
lean_inc(v_val_2543_);
lean_dec_ref(v_fst_2542_);
if (lean_obj_tag(v_val_2543_) == 0)
{
goto v___jp_2496_;
}
else
{
lean_object* v_val_2544_; 
v_val_2544_ = lean_ctor_get(v_val_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref(v_val_2543_);
v_next_2472_ = v_val_2544_;
v___y_2473_ = v___y_2421_;
v___y_2474_ = v___y_2422_;
v___y_2475_ = v___y_2423_;
v___y_2476_ = v___y_2424_;
goto v___jp_2471_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2545_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2540_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2540_);
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
else
{
lean_object* v___x_2554_; 
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
if (v_isShared_2470_ == 0)
{
v___x_2554_ = v___x_2469_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_fst_2466_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_snd_2467_);
v___x_2554_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
v___jp_2471_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
lean_inc(v_next_2472_);
v___x_2477_ = lean_array_push(v_fst_2466_, v_next_2472_);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_array_get_size(v_snd_2467_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2481_ = lean_nat_dec_lt(v___x_2478_, v___x_2479_);
if (v___x_2481_ == 0)
{
lean_dec(v_snd_2467_);
v___y_2427_ = v___y_2476_;
v___y_2428_ = v___y_2474_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___x_2477_;
v___y_2431_ = v_next_2472_;
v___y_2432_ = v___y_2473_;
v___y_2433_ = v___x_2480_;
goto v___jp_2426_;
}
else
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_nat_dec_le(v___x_2479_, v___x_2479_);
if (v___x_2482_ == 0)
{
if (v___x_2481_ == 0)
{
lean_dec(v_snd_2467_);
v___y_2427_ = v___y_2476_;
v___y_2428_ = v___y_2474_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___x_2477_;
v___y_2431_ = v_next_2472_;
v___y_2432_ = v___y_2473_;
v___y_2433_ = v___x_2480_;
goto v___jp_2426_;
}
else
{
size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = ((size_t)0ULL);
v___x_2484_ = lean_usize_of_nat(v___x_2479_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2472_, v_snd_2467_, v___x_2483_, v___x_2484_, v___x_2480_);
lean_dec(v_snd_2467_);
v___y_2427_ = v___y_2476_;
v___y_2428_ = v___y_2474_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___x_2477_;
v___y_2431_ = v_next_2472_;
v___y_2432_ = v___y_2473_;
v___y_2433_ = v___x_2485_;
goto v___jp_2426_;
}
}
else
{
size_t v___x_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = ((size_t)0ULL);
v___x_2487_ = lean_usize_of_nat(v___x_2479_);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2472_, v_snd_2467_, v___x_2486_, v___x_2487_, v___x_2480_);
lean_dec(v_snd_2467_);
v___y_2427_ = v___y_2476_;
v___y_2428_ = v___y_2474_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___x_2477_;
v___y_2431_ = v_next_2472_;
v___y_2432_ = v___y_2473_;
v___y_2433_ = v___x_2488_;
goto v___jp_2426_;
}
}
}
v___jp_2489_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_array_get_borrowed(v___x_2494_, v_snd_2467_, v___x_2494_);
lean_inc(v___x_2495_);
v_next_2472_ = v___x_2495_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
v___y_2475_ = v___y_2492_;
v___y_2476_ = v___y_2493_;
goto v___jp_2471_;
}
v___jp_2496_:
{
lean_object* v_options_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v_options_2497_ = lean_ctor_get(v___y_2423_, 2);
v___x_2498_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2499_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2497_, v___x_2498_);
if (v___x_2499_ == 0)
{
v___y_2490_ = v___y_2421_;
v___y_2491_ = v___y_2422_;
v___y_2492_ = v___y_2423_;
v___y_2493_ = v___y_2424_;
goto v___jp_2489_;
}
else
{
size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v_sz_2500_ = lean_array_size(v_snd_2467_);
v___x_2501_ = ((size_t)0ULL);
lean_inc(v_snd_2467_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2415_, v_sz_2500_, v___x_2501_, v_snd_2467_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = lean_array_to_list(v_a_2503_);
v___x_2505_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2506_ = l_Lean_MessageData_joinSep(v___x_2504_, v___x_2505_);
v___x_2507_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2417_);
v___x_2508_ = l_Lean_MessageData_ofExpr(v_inst_2417_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
lean_inc_ref(v_a_2418_);
v___x_2512_ = l_Lean_indentExpr(v_a_2418_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___x_2506_);
v___x_2517_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2516_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref(v___x_2517_);
v___y_2490_ = v___y_2421_;
v___y_2491_ = v___y_2422_;
v___y_2492_ = v___y_2423_;
v___y_2493_ = v___y_2424_;
goto v___jp_2489_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_inst_2417_);
v_a_2526_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2502_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2502_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2558_, lean_object* v_argVars_2559_, lean_object* v_inst_2560_, lean_object* v_a_2561_, lean_object* v_projInfo_x3f_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2558_, v_argVars_2559_, v_inst_2560_, v_a_2561_, v_projInfo_x3f_2562_, v_b_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v_projInfo_x3f_2562_);
lean_dec_ref(v_argVars_2559_);
lean_dec_ref(v_fst_2558_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2570_, size_t v_sz_2571_, size_t v_i_2572_, lean_object* v_bs_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_usize_dec_lt(v_i_2572_, v_sz_2571_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_bs_2573_);
return v___x_2580_;
}
else
{
lean_object* v_v_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_v_2581_ = lean_array_uget_borrowed(v_bs_2573_, v_i_2572_);
v___x_2582_ = l_Lean_instInhabitedExpr;
v___x_2583_ = lean_array_get_borrowed(v___x_2582_, v_argVars_2570_, v_v_2581_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___x_2583_);
v___x_2584_ = lean_infer_type(v___x_2583_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; lean_object* v_bs_x27_2587_; lean_object* v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = lean_unsigned_to_nat(0u);
v_bs_x27_2587_ = lean_array_uset(v_bs_2573_, v_i_2572_, v___x_2586_);
v___x_2588_ = l_Lean_indentExpr(v_a_2585_);
v___x_2589_ = ((size_t)1ULL);
v___x_2590_ = lean_usize_add(v_i_2572_, v___x_2589_);
v___x_2591_ = lean_array_uset(v_bs_x27_2587_, v_i_2572_, v___x_2588_);
v_i_2572_ = v___x_2590_;
v_bs_2573_ = v___x_2591_;
goto _start;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_bs_2573_);
v_a_2593_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2584_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2584_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2601_, lean_object* v_sz_2602_, lean_object* v_i_2603_, lean_object* v_bs_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
size_t v_sz_boxed_2610_; size_t v_i_boxed_2611_; lean_object* v_res_2612_; 
v_sz_boxed_2610_ = lean_unbox_usize(v_sz_2602_);
lean_dec(v_sz_2602_);
v_i_boxed_2611_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2601_, v_sz_boxed_2610_, v_i_boxed_2611_, v_bs_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_argVars_2601_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v___x_2615_; 
v___x_2615_ = l_List_reverse___redArg(v_a_2614_);
return v___x_2615_;
}
else
{
lean_object* v_head_2616_; lean_object* v_tail_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2628_; 
v_head_2616_ = lean_ctor_get(v_a_2613_, 0);
v_tail_2617_ = lean_ctor_get(v_a_2613_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2619_ = v_a_2613_;
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_tail_2617_);
lean_inc(v_head_2616_);
lean_dec(v_a_2613_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2621_ = l_Nat_reprFast(v_head_2616_);
v___x_2622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
v___x_2623_ = l_Lean_MessageData_ofFormat(v___x_2622_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v_a_2614_);
lean_ctor_set(v___x_2619_, 0, v___x_2623_);
v___x_2625_ = v___x_2619_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_a_2614_);
v___x_2625_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v_a_2613_ = v_tail_2617_;
v_a_2614_ = v___x_2625_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2629_; double v___x_2630_; 
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_float_of_nat(v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_ref_2640_; lean_object* v___x_2641_; lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2686_; 
v_ref_2640_ = lean_ctor_get(v___y_2637_, 5);
v___x_2641_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2686_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2686_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v_traceState_2647_; lean_object* v_env_2648_; lean_object* v_nextMacroScope_2649_; lean_object* v_ngen_2650_; lean_object* v_auxDeclNGen_2651_; lean_object* v_cache_2652_; lean_object* v_messages_2653_; lean_object* v_infoState_2654_; lean_object* v_snapshotTasks_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2685_; 
v___x_2646_ = lean_st_ref_take(v___y_2638_);
v_traceState_2647_ = lean_ctor_get(v___x_2646_, 4);
v_env_2648_ = lean_ctor_get(v___x_2646_, 0);
v_nextMacroScope_2649_ = lean_ctor_get(v___x_2646_, 1);
v_ngen_2650_ = lean_ctor_get(v___x_2646_, 2);
v_auxDeclNGen_2651_ = lean_ctor_get(v___x_2646_, 3);
v_cache_2652_ = lean_ctor_get(v___x_2646_, 5);
v_messages_2653_ = lean_ctor_get(v___x_2646_, 6);
v_infoState_2654_ = lean_ctor_get(v___x_2646_, 7);
v_snapshotTasks_2655_ = lean_ctor_get(v___x_2646_, 8);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snapshotTasks_2655_);
lean_inc(v_infoState_2654_);
lean_inc(v_messages_2653_);
lean_inc(v_cache_2652_);
lean_inc(v_traceState_2647_);
lean_inc(v_auxDeclNGen_2651_);
lean_inc(v_ngen_2650_);
lean_inc(v_nextMacroScope_2649_);
lean_inc(v_env_2648_);
lean_dec(v___x_2646_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
uint64_t v_tid_2659_; lean_object* v_traces_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2684_; 
v_tid_2659_ = lean_ctor_get_uint64(v_traceState_2647_, sizeof(void*)*1);
v_traces_2660_ = lean_ctor_get(v_traceState_2647_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_traceState_2647_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2662_ = v_traceState_2647_;
v_isShared_2663_ = v_isSharedCheck_2684_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_traces_2660_);
lean_dec(v_traceState_2647_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2684_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; double v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2666_ = 0;
v___x_2667_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2668_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2668_, 0, v_cls_2633_);
lean_ctor_set(v___x_2668_, 1, v___x_2664_);
lean_ctor_set(v___x_2668_, 2, v___x_2667_);
lean_ctor_set_float(v___x_2668_, sizeof(void*)*3, v___x_2665_);
lean_ctor_set_float(v___x_2668_, sizeof(void*)*3 + 8, v___x_2665_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*3 + 16, v___x_2666_);
v___x_2669_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2670_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v_a_2642_);
lean_ctor_set(v___x_2670_, 2, v___x_2669_);
lean_inc(v_ref_2640_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_ref_2640_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_PersistentArray_push___redArg(v_traces_2660_, v___x_2671_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2672_);
v___x_2674_ = v___x_2662_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2672_);
lean_ctor_set_uint64(v_reuseFailAlloc_2683_, sizeof(void*)*1, v_tid_2659_);
v___x_2674_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 4, v___x_2674_);
v___x_2676_ = v___x_2657_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_env_2648_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_nextMacroScope_2649_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_ngen_2650_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_auxDeclNGen_2651_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v_cache_2652_);
lean_ctor_set(v_reuseFailAlloc_2682_, 6, v_messages_2653_);
lean_ctor_set(v_reuseFailAlloc_2682_, 7, v_infoState_2654_);
lean_ctor_set(v_reuseFailAlloc_2682_, 8, v_snapshotTasks_2655_);
v___x_2676_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_st_ref_set(v___y_2638_, v___x_2676_);
v___x_2678_ = lean_box(0);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2678_);
v___x_2680_ = v___x_2644_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2687_, v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2694_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2704_ = l_Lean_Name_append(v___x_2703_, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2710_ = l_Lean_stringToMessageData(v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2717_, lean_object* v_fst_2718_, lean_object* v_fst_2719_, lean_object* v_inst_2720_, lean_object* v_a_2721_, lean_object* v_projInfo_x3f_2722_, lean_object* v_argVars_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2717_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_dummy_2732_; lean_object* v_nargs_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; size_t v_sz_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v_dummy_2732_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2733_ = l_Lean_Expr_getAppNumArgs(v_a_2717_);
lean_inc(v_nargs_2733_);
v___x_2734_ = lean_mk_array(v_nargs_2733_, v_dummy_2732_);
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_sub(v_nargs_2733_, v___x_2735_);
lean_dec(v_nargs_2733_);
lean_inc_ref(v_a_2717_);
v___x_2737_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2717_, v___x_2734_, v___x_2736_);
v___x_2738_ = lean_array_get_size(v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v___x_2738_);
v_sz_2741_ = lean_array_size(v___x_2737_);
v___x_2742_ = ((size_t)0ULL);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2731_, v_fst_2718_, v_argVars_2723_, v___x_2737_, v_sz_2741_, v___x_2742_, v___x_2740_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec_ref(v___x_2737_);
lean_dec(v_a_2731_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec_ref(v___x_2743_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2745_ = lean_array_get_size(v_fst_2718_);
v___x_2746_ = l_List_range(v___x_2745_);
v___x_2747_ = lean_box(0);
v___x_2748_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2719_, v___x_2746_, v___x_2747_);
v___x_2749_ = lean_array_mk(v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2744_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
lean_inc_ref(v_inst_2720_);
v___x_2751_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2718_, v_argVars_2723_, v_inst_2720_, v_a_2721_, v_projInfo_x3f_2722_, v___x_2750_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2844_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2844_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2844_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_fst_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2842_; 
v_fst_2756_ = lean_ctor_get(v_a_2752_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_a_2752_, 1);
lean_dec(v_unused_2843_);
v___x_2758_ = v_a_2752_;
v_isShared_2759_ = v_isSharedCheck_2842_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_fst_2756_);
lean_dec(v_a_2752_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2842_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_options_2764_; lean_object* v_inheritedTraceOptions_2765_; lean_object* v___y_2766_; lean_object* v_options_2822_; lean_object* v_inheritedTraceOptions_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v_options_2822_ = lean_ctor_get(v___y_2727_, 2);
v_inheritedTraceOptions_2823_ = lean_ctor_get(v___y_2727_, 13);
v___x_2824_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2825_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2822_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_dec_ref(v_a_2717_);
v___y_2761_ = v___y_2725_;
v___y_2762_ = v___y_2726_;
v___y_2763_ = v___y_2727_;
v_options_2764_ = v_options_2822_;
v_inheritedTraceOptions_2765_ = v_inheritedTraceOptions_2823_;
v___y_2766_ = v___y_2728_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2826_; lean_object* v_a_2827_; uint8_t v___x_2828_; 
v___x_2826_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2717_, v___y_2726_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = l_Lean_Expr_hasExprMVar(v_a_2827_);
if (v___x_2828_ == 0)
{
lean_dec(v_a_2827_);
v___y_2761_ = v___y_2725_;
v___y_2762_ = v___y_2726_;
v___y_2763_ = v___y_2727_;
v_options_2764_ = v_options_2822_;
v_inheritedTraceOptions_2765_ = v_inheritedTraceOptions_2823_;
v___y_2766_ = v___y_2728_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_del_object(v___x_2758_);
lean_dec(v_fst_2756_);
lean_del_object(v___x_2754_);
lean_dec_ref(v_inst_2720_);
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2830_ = l_Lean_Expr_setPPExplicit(v_a_2827_, v___x_2828_);
v___x_2831_ = l_Lean_indentExpr(v___x_2830_);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2829_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2832_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
v___jp_2760_:
{
uint8_t v_hasTrace_2767_; 
v_hasTrace_2767_ = lean_ctor_get_uint8(v_options_2764_, sizeof(void*)*1);
if (v_hasTrace_2767_ == 0)
{
lean_object* v___x_2769_; 
lean_del_object(v___x_2758_);
lean_dec_ref(v_inst_2720_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_fst_2756_);
v___x_2769_ = v___x_2754_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_fst_2756_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2772_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2765_, v_options_2764_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2775_; 
lean_del_object(v___x_2758_);
lean_dec_ref(v_inst_2720_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_fst_2756_);
v___x_2775_ = v___x_2754_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_fst_2756_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
size_t v_sz_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2754_);
v_sz_2777_ = lean_array_size(v_fst_2756_);
lean_inc(v_fst_2756_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2723_, v_sz_2777_, v___x_2742_, v_fst_2756_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2766_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2781_ = l_Lean_MessageData_ofExpr(v_inst_2720_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 7);
lean_ctor_set(v___x_2758_, 1, v___x_2781_);
lean_ctor_set(v___x_2758_, 0, v___x_2780_);
v___x_2783_ = v___x_2758_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
lean_inc(v_fst_2756_);
v___x_2786_ = lean_array_to_list(v_fst_2756_);
v___x_2787_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2786_, v___x_2747_);
v___x_2788_ = l_Lean_MessageData_ofList(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2785_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_array_to_list(v_a_2779_);
v___x_2793_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2794_ = l_Lean_MessageData_joinSep(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2791_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2771_, v___x_2795_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2766_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2796_, 0);
lean_dec(v_unused_2804_);
v___x_2798_ = v___x_2796_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v_fst_2756_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_fst_2756_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_fst_2756_);
v_a_2805_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2796_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2796_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_del_object(v___x_2758_);
lean_dec(v_fst_2756_);
lean_dec_ref(v_inst_2720_);
v_a_2814_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2778_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2778_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
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
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_inst_2720_);
lean_dec_ref(v_a_2717_);
v_a_2845_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2751_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2751_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v_a_2721_);
lean_dec_ref(v_inst_2720_);
lean_dec_ref(v_a_2717_);
v_a_2853_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2743_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2743_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_dec_ref(v_a_2721_);
lean_dec_ref(v_inst_2720_);
lean_dec_ref(v_a_2717_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2861_, lean_object* v_fst_2862_, lean_object* v_fst_2863_, lean_object* v_inst_2864_, lean_object* v_a_2865_, lean_object* v_projInfo_x3f_2866_, lean_object* v_argVars_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2861_, v_fst_2862_, v_fst_2863_, v_inst_2864_, v_a_2865_, v_projInfo_x3f_2866_, v_argVars_2867_, v_x_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec_ref(v_x_2868_);
lean_dec_ref(v_argVars_2867_);
lean_dec(v_projInfo_x3f_2866_);
lean_dec_ref(v_fst_2863_);
lean_dec_ref(v_fst_2862_);
return v_res_2874_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2875_; uint64_t v___x_2876_; 
v___x_2875_ = 2;
v___x_2876_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2877_, lean_object* v_projInfo_x3f_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; uint8_t v_foApprox_2885_; uint8_t v_ctxApprox_2886_; uint8_t v_quasiPatternApprox_2887_; uint8_t v_constApprox_2888_; uint8_t v_isDefEqStuckEx_2889_; uint8_t v_unificationHints_2890_; uint8_t v_proofIrrelevance_2891_; uint8_t v_assignSyntheticOpaque_2892_; uint8_t v_offsetCnstrs_2893_; uint8_t v_etaStruct_2894_; uint8_t v_univApprox_2895_; uint8_t v_iota_2896_; uint8_t v_beta_2897_; uint8_t v_proj_2898_; uint8_t v_zeta_2899_; uint8_t v_zetaDelta_2900_; uint8_t v_zetaUnused_2901_; uint8_t v_zetaHave_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2967_; 
v___x_2884_ = l_Lean_Meta_Context_config(v_a_2879_);
v_foApprox_2885_ = lean_ctor_get_uint8(v___x_2884_, 0);
v_ctxApprox_2886_ = lean_ctor_get_uint8(v___x_2884_, 1);
v_quasiPatternApprox_2887_ = lean_ctor_get_uint8(v___x_2884_, 2);
v_constApprox_2888_ = lean_ctor_get_uint8(v___x_2884_, 3);
v_isDefEqStuckEx_2889_ = lean_ctor_get_uint8(v___x_2884_, 4);
v_unificationHints_2890_ = lean_ctor_get_uint8(v___x_2884_, 5);
v_proofIrrelevance_2891_ = lean_ctor_get_uint8(v___x_2884_, 6);
v_assignSyntheticOpaque_2892_ = lean_ctor_get_uint8(v___x_2884_, 7);
v_offsetCnstrs_2893_ = lean_ctor_get_uint8(v___x_2884_, 8);
v_etaStruct_2894_ = lean_ctor_get_uint8(v___x_2884_, 10);
v_univApprox_2895_ = lean_ctor_get_uint8(v___x_2884_, 11);
v_iota_2896_ = lean_ctor_get_uint8(v___x_2884_, 12);
v_beta_2897_ = lean_ctor_get_uint8(v___x_2884_, 13);
v_proj_2898_ = lean_ctor_get_uint8(v___x_2884_, 14);
v_zeta_2899_ = lean_ctor_get_uint8(v___x_2884_, 15);
v_zetaDelta_2900_ = lean_ctor_get_uint8(v___x_2884_, 16);
v_zetaUnused_2901_ = lean_ctor_get_uint8(v___x_2884_, 17);
v_zetaHave_2902_ = lean_ctor_get_uint8(v___x_2884_, 18);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2904_ = v___x_2884_;
v_isShared_2905_ = v_isSharedCheck_2967_;
goto v_resetjp_2903_;
}
else
{
lean_dec(v___x_2884_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2967_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
uint8_t v_trackZetaDelta_2906_; lean_object* v_zetaDeltaSet_2907_; lean_object* v_lctx_2908_; lean_object* v_localInstances_2909_; lean_object* v_defEqCtx_x3f_2910_; lean_object* v_synthPendingDepth_2911_; lean_object* v_canUnfold_x3f_2912_; uint8_t v_univApprox_2913_; uint8_t v_inTypeClassResolution_2914_; uint8_t v_cacheInferType_2915_; uint8_t v___x_2916_; lean_object* v_config_2918_; 
v_trackZetaDelta_2906_ = lean_ctor_get_uint8(v_a_2879_, sizeof(void*)*7);
v_zetaDeltaSet_2907_ = lean_ctor_get(v_a_2879_, 1);
v_lctx_2908_ = lean_ctor_get(v_a_2879_, 2);
v_localInstances_2909_ = lean_ctor_get(v_a_2879_, 3);
v_defEqCtx_x3f_2910_ = lean_ctor_get(v_a_2879_, 4);
v_synthPendingDepth_2911_ = lean_ctor_get(v_a_2879_, 5);
v_canUnfold_x3f_2912_ = lean_ctor_get(v_a_2879_, 6);
v_univApprox_2913_ = lean_ctor_get_uint8(v_a_2879_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2914_ = lean_ctor_get_uint8(v_a_2879_, sizeof(void*)*7 + 2);
v_cacheInferType_2915_ = lean_ctor_get_uint8(v_a_2879_, sizeof(void*)*7 + 3);
v___x_2916_ = 2;
if (v_isShared_2905_ == 0)
{
v_config_2918_ = v___x_2904_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 0, v_foApprox_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 1, v_ctxApprox_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 2, v_quasiPatternApprox_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 3, v_constApprox_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 4, v_isDefEqStuckEx_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 5, v_unificationHints_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 6, v_proofIrrelevance_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 7, v_assignSyntheticOpaque_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 8, v_offsetCnstrs_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 10, v_etaStruct_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 11, v_univApprox_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 12, v_iota_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 13, v_beta_2897_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 14, v_proj_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 15, v_zeta_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 16, v_zetaDelta_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 17, v_zetaUnused_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, 18, v_zetaHave_2902_);
v_config_2918_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v_key_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_ctor_set_uint8(v_config_2918_, 9, v___x_2916_);
v___x_2919_ = l_Lean_Meta_Context_configKey(v_a_2879_);
v___x_2920_ = 2ULL;
v___x_2921_ = lean_uint64_shift_right(v___x_2919_, v___x_2920_);
v___x_2922_ = lean_uint64_shift_left(v___x_2921_, v___x_2920_);
v___x_2923_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2924_ = lean_uint64_lor(v___x_2922_, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2925_, 0, v_config_2918_);
lean_ctor_set_uint64(v___x_2925_, sizeof(void*)*1, v_key_2924_);
lean_inc(v_canUnfold_x3f_2912_);
lean_inc(v_synthPendingDepth_2911_);
lean_inc(v_defEqCtx_x3f_2910_);
lean_inc_ref(v_localInstances_2909_);
lean_inc_ref(v_lctx_2908_);
lean_inc(v_zetaDeltaSet_2907_);
v___x_2926_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v_zetaDeltaSet_2907_);
lean_ctor_set(v___x_2926_, 2, v_lctx_2908_);
lean_ctor_set(v___x_2926_, 3, v_localInstances_2909_);
lean_ctor_set(v___x_2926_, 4, v_defEqCtx_x3f_2910_);
lean_ctor_set(v___x_2926_, 5, v_synthPendingDepth_2911_);
lean_ctor_set(v___x_2926_, 6, v_canUnfold_x3f_2912_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7, v_trackZetaDelta_2906_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 1, v_univApprox_2913_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2914_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*7 + 3, v_cacheInferType_2915_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc_ref(v___x_2926_);
lean_inc_ref(v_inst_2877_);
v___x_2927_ = lean_infer_type(v_inst_2877_, v___x_2926_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc_n(v_a_2928_, 2);
lean_dec_ref(v___x_2927_);
v___x_2929_ = lean_box(0);
v___x_2930_ = 0;
v___x_2931_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2928_, v___x_2929_, v___x_2930_, v___x_2926_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_snd_2933_; lean_object* v_fst_2934_; lean_object* v_fst_2935_; lean_object* v_snd_2936_; lean_object* v___x_2937_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v_snd_2933_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_snd_2933_);
v_fst_2934_ = lean_ctor_get(v_a_2932_, 0);
lean_inc(v_fst_2934_);
lean_dec(v_a_2932_);
v_fst_2935_ = lean_ctor_get(v_snd_2933_, 0);
lean_inc(v_fst_2935_);
v_snd_2936_ = lean_ctor_get(v_snd_2933_, 1);
lean_inc(v_snd_2936_);
lean_dec(v_snd_2933_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc_ref(v___x_2926_);
v___x_2937_ = lean_whnf(v_snd_2936_, v___x_2926_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___f_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2937_);
lean_inc(v_a_2928_);
v___f_2939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2939_, 0, v_a_2938_);
lean_closure_set(v___f_2939_, 1, v_fst_2934_);
lean_closure_set(v___f_2939_, 2, v_fst_2935_);
lean_closure_set(v___f_2939_, 3, v_inst_2877_);
lean_closure_set(v___f_2939_, 4, v_a_2928_);
lean_closure_set(v___f_2939_, 5, v_projInfo_x3f_2878_);
v___x_2940_ = 0;
v___x_2941_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2928_, v___f_2939_, v___x_2940_, v___x_2940_, v___x_2926_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec_ref(v___x_2926_);
return v___x_2941_;
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_fst_2935_);
lean_dec(v_fst_2934_);
lean_dec(v_a_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v_projInfo_x3f_2878_);
lean_dec_ref(v_inst_2877_);
v_a_2942_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2937_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2937_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_a_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v_projInfo_x3f_2878_);
lean_dec_ref(v_inst_2877_);
v_a_2950_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2931_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2931_);
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
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v___x_2926_);
lean_dec(v_projInfo_x3f_2878_);
lean_dec_ref(v_inst_2877_);
v_a_2958_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2927_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2927_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_2968_, lean_object* v_projInfo_x3f_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_2968_, v_projInfo_x3f_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_2976_, lean_object* v___x_2977_, lean_object* v_a_2978_, lean_object* v_inst_2979_, lean_object* v_R_2980_, lean_object* v_a_2981_, lean_object* v_b_2982_, lean_object* v_c_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2976_, v___x_2977_, v_a_2978_, v_a_2981_, v_b_2982_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_2990_, lean_object* v___x_2991_, lean_object* v_a_2992_, lean_object* v_inst_2993_, lean_object* v_R_2994_, lean_object* v_a_2995_, lean_object* v_b_2996_, lean_object* v_c_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_2990_, v___x_2991_, v_a_2992_, v_inst_2993_, v_R_2994_, v_a_2995_, v_b_2996_, v_c_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_a_2992_);
lean_dec(v___x_2991_);
lean_dec(v_upperBound_2990_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3012_, v_msg_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3019_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v___x_3020_, lean_object* v_as_3021_, size_t v_i_3022_, size_t v_stop_3023_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_eq(v_i_3022_, v_stop_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = lean_array_uget_borrowed(v_as_3021_, v_i_3022_);
v___x_3026_ = l_Lean_Expr_containsFVar(v___x_3025_, v___x_3020_);
if (v___x_3026_ == 0)
{
size_t v___x_3027_; size_t v___x_3028_; 
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_add(v_i_3022_, v___x_3027_);
v_i_3022_ = v___x_3028_;
goto _start;
}
else
{
return v___x_3026_;
}
}
else
{
uint8_t v___x_3030_; 
v___x_3030_ = 0;
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v___x_3031_, lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_){
_start:
{
size_t v_i_boxed_3035_; size_t v_stop_boxed_3036_; uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_i_boxed_3035_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3036_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3037_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(v___x_3031_, v_as_3032_, v_i_boxed_3035_, v_stop_boxed_3036_);
lean_dec_ref(v_as_3032_);
lean_dec(v___x_3031_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__0));
v___x_3041_ = l_Lean_stringToMessageData(v___x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object* v_ty_3042_, lean_object* v_a_3043_, lean_object* v_as_3044_, size_t v_i_3045_, size_t v_stop_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_a_3054_; uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_eq(v_i_3045_, v_stop_3046_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v_fst_3060_; lean_object* v_snd_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3115_; 
v___x_3059_ = lean_array_uget(v_as_3044_, v_i_3045_);
v_fst_3060_ = lean_ctor_get(v___x_3059_, 0);
v_snd_3061_ = lean_ctor_get(v___x_3059_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3063_ = v___x_3059_;
v_isShared_3064_ = v_isSharedCheck_3115_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_snd_3061_);
lean_inc(v_fst_3060_);
lean_dec(v___x_3059_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3115_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = l_Lean_Expr_fvarId_x21(v_fst_3060_);
lean_inc(v___x_3065_);
v___x_3066_ = l_Lean_FVarId_getDecl___redArg(v___x_3065_, v___y_3048_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; uint8_t v___y_3069_; uint8_t v___x_3088_; uint8_t v___x_3089_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref(v___x_3066_);
v___x_3088_ = l_Lean_LocalDecl_binderInfo(v_a_3067_);
lean_dec(v_a_3067_);
v___x_3089_ = l_Lean_BinderInfo_isInstImplicit(v___x_3088_);
if (v___x_3089_ == 0)
{
uint8_t v___x_3090_; 
v___x_3090_ = l_Lean_Expr_containsFVar(v_ty_3042_, v___x_3065_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_array_3095_; lean_object* v_start_3096_; lean_object* v_stop_3097_; lean_object* v___y_3099_; uint8_t v___x_3104_; 
v___x_3091_ = lean_unsigned_to_nat(1u);
v___x_3092_ = lean_nat_add(v_snd_3061_, v___x_3091_);
lean_dec(v_snd_3061_);
v___x_3093_ = lean_array_get_size(v_a_3043_);
lean_inc_ref(v_a_3043_);
v___x_3094_ = l_Array_toSubarray___redArg(v_a_3043_, v___x_3092_, v___x_3093_);
v_array_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_ref(v_array_3095_);
v_start_3096_ = lean_ctor_get(v___x_3094_, 1);
lean_inc(v_start_3096_);
v_stop_3097_ = lean_ctor_get(v___x_3094_, 2);
lean_inc(v_stop_3097_);
lean_dec_ref(v___x_3094_);
v___x_3104_ = lean_nat_dec_lt(v_start_3096_, v_stop_3097_);
if (v___x_3104_ == 0)
{
lean_dec(v_stop_3097_);
lean_dec(v_start_3096_);
lean_dec_ref(v_array_3095_);
lean_dec(v___x_3065_);
v___y_3069_ = v___x_3090_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3105_ = lean_array_get_size(v_array_3095_);
v___x_3106_ = lean_nat_dec_le(v_stop_3097_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_dec(v_stop_3097_);
v___y_3099_ = v___x_3105_;
goto v___jp_3098_;
}
else
{
v___y_3099_ = v_stop_3097_;
goto v___jp_3098_;
}
}
v___jp_3098_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_nat_dec_lt(v_start_3096_, v___y_3099_);
if (v___x_3100_ == 0)
{
lean_dec(v___y_3099_);
lean_dec(v_start_3096_);
lean_dec_ref(v_array_3095_);
lean_dec(v___x_3065_);
v___y_3069_ = v___x_3090_;
goto v___jp_3068_;
}
else
{
size_t v___x_3101_; size_t v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = lean_usize_of_nat(v_start_3096_);
lean_dec(v_start_3096_);
v___x_3102_ = lean_usize_of_nat(v___y_3099_);
lean_dec(v___y_3099_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_checkImpossibleInstance_spec__1(v___x_3065_, v_array_3095_, v___x_3101_, v___x_3102_);
lean_dec_ref(v_array_3095_);
lean_dec(v___x_3065_);
v___y_3069_ = v___x_3103_;
goto v___jp_3068_;
}
}
}
else
{
lean_dec(v___x_3065_);
lean_del_object(v___x_3063_);
lean_dec(v_snd_3061_);
lean_dec(v_fst_3060_);
v_a_3054_ = v_b_3047_;
goto v___jp_3053_;
}
}
else
{
lean_dec(v___x_3065_);
lean_del_object(v___x_3063_);
lean_dec(v_snd_3061_);
lean_dec(v_fst_3060_);
v_a_3054_ = v_b_3047_;
goto v___jp_3053_;
}
v___jp_3068_:
{
if (v___y_3069_ == 0)
{
lean_object* v___x_3070_; 
lean_inc(v___y_3051_);
lean_inc_ref(v___y_3050_);
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v_fst_3060_);
v___x_3070_ = lean_infer_type(v_fst_3060_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = l_Lean_MessageData_ofExpr(v_fst_3060_);
v___x_3073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___closed__1);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 7);
lean_ctor_set(v___x_3063_, 1, v___x_3073_);
lean_ctor_set(v___x_3063_, 0, v___x_3072_);
v___x_3075_ = v___x_3063_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = l_Lean_MessageData_ofExpr(v_a_3071_);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_array_push(v_b_3047_, v___x_3077_);
v_a_3054_ = v___x_3078_;
goto v___jp_3053_;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_del_object(v___x_3063_);
lean_dec(v_fst_3060_);
lean_dec_ref(v_b_3047_);
lean_dec_ref(v_a_3043_);
v_a_3080_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3070_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3070_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_del_object(v___x_3063_);
lean_dec(v_fst_3060_);
v_a_3054_ = v_b_3047_;
goto v___jp_3053_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v___x_3065_);
lean_del_object(v___x_3063_);
lean_dec(v_snd_3061_);
lean_dec(v_fst_3060_);
lean_dec_ref(v_b_3047_);
lean_dec_ref(v_a_3043_);
v_a_3107_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3066_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3066_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
else
{
lean_object* v___x_3116_; 
lean_dec_ref(v_a_3043_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_b_3047_);
return v___x_3116_;
}
v___jp_3053_:
{
size_t v___x_3055_; size_t v___x_3056_; 
v___x_3055_ = ((size_t)1ULL);
v___x_3056_ = lean_usize_add(v_i_3045_, v___x_3055_);
v_i_3045_ = v___x_3056_;
v_b_3047_ = v_a_3054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object* v_ty_3117_, lean_object* v_a_3118_, lean_object* v_as_3119_, lean_object* v_i_3120_, lean_object* v_stop_3121_, lean_object* v_b_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
size_t v_i_boxed_3128_; size_t v_stop_boxed_3129_; lean_object* v_res_3130_; 
v_i_boxed_3128_ = lean_unbox_usize(v_i_3120_);
lean_dec(v_i_3120_);
v_stop_boxed_3129_ = lean_unbox_usize(v_stop_3121_);
lean_dec(v_stop_3121_);
v_res_3130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3117_, v_a_3118_, v_as_3119_, v_i_boxed_3128_, v_stop_boxed_3129_, v_b_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v_as_3119_);
lean_dec_ref(v_ty_3117_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_ty_3131_, lean_object* v_a_3132_, lean_object* v_as_3133_, lean_object* v_start_3134_, lean_object* v_stop_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_3142_ = lean_nat_dec_lt(v_start_3134_, v_stop_3135_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec_ref(v_a_3132_);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3144_ = lean_array_get_size(v_as_3133_);
v___x_3145_ = lean_nat_dec_le(v_stop_3135_, v___x_3144_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_nat_dec_lt(v_start_3134_, v___x_3144_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec_ref(v_a_3132_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3141_);
return v___x_3147_;
}
else
{
size_t v___x_3148_; size_t v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_usize_of_nat(v_start_3134_);
v___x_3149_ = lean_usize_of_nat(v___x_3144_);
v___x_3150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3131_, v_a_3132_, v_as_3133_, v___x_3148_, v___x_3149_, v___x_3141_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3150_;
}
}
else
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_usize_of_nat(v_start_3134_);
v___x_3152_ = lean_usize_of_nat(v_stop_3135_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_ty_3131_, v_a_3132_, v_as_3133_, v___x_3151_, v___x_3152_, v___x_3141_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_ty_3154_, lean_object* v_a_3155_, lean_object* v_as_3156_, lean_object* v_start_3157_, lean_object* v_stop_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_ty_3154_, v_a_3155_, v_as_3156_, v_start_3157_, v_stop_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v_stop_3158_);
lean_dec(v_start_3157_);
lean_dec_ref(v_as_3156_);
lean_dec_ref(v_ty_3154_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(size_t v_sz_3165_, size_t v_i_3166_, lean_object* v_bs_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3174_, 0, v_bs_3167_);
return v___x_3174_;
}
else
{
lean_object* v_v_3175_; lean_object* v___x_3176_; 
v_v_3175_ = lean_array_uget_borrowed(v_bs_3167_, v_i_3166_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
lean_inc(v_v_3175_);
v___x_3176_ = lean_infer_type(v_v_3175_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v_bs_x27_3179_; size_t v___x_3180_; size_t v___x_3181_; lean_object* v___x_3182_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v_bs_x27_3179_ = lean_array_uset(v_bs_3167_, v_i_3166_, v___x_3178_);
v___x_3180_ = ((size_t)1ULL);
v___x_3181_ = lean_usize_add(v_i_3166_, v___x_3180_);
v___x_3182_ = lean_array_uset(v_bs_x27_3179_, v_i_3166_, v_a_3177_);
v_i_3166_ = v___x_3181_;
v_bs_3167_ = v___x_3182_;
goto _start;
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_bs_3167_);
v_a_3184_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3176_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3176_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_sz_3192_, lean_object* v_i_3193_, lean_object* v_bs_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
size_t v_sz_boxed_3200_; size_t v_i_boxed_3201_; lean_object* v_res_3202_; 
v_sz_boxed_3200_ = lean_unbox_usize(v_sz_3192_);
lean_dec(v_sz_3192_);
v_i_boxed_3201_ = lean_unbox_usize(v_i_3193_);
lean_dec(v_i_3193_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_sz_boxed_3200_, v_i_boxed_3201_, v_bs_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3202_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1));
v___x_3207_ = l_Lean_MessageData_ofFormat(v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3));
v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
return v___x_3210_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5));
v___x_3213_ = l_Lean_stringToMessageData(v___x_3212_);
return v___x_3213_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v___x_3218_ = l_Lean_MessageData_ofFormat(v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v_c_3219_, lean_object* v_args_3220_, lean_object* v_ty_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v_sz_3227_ = lean_array_size(v_args_3220_);
v___x_3228_ = ((size_t)0ULL);
lean_inc_ref(v_args_3220_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_sz_3227_, v___x_3228_, v_args_3220_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = l_Array_zipIdx___redArg(v_args_3220_, v___x_3231_);
lean_dec_ref(v_args_3220_);
v___x_3233_ = lean_array_get_size(v___x_3232_);
v___x_3234_ = l_Array_filterMapM___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_ty_3221_, v_a_3230_, v___x_3232_, v___x_3231_, v___x_3233_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec_ref(v___x_3232_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3257_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3257_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3257_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = lean_array_get_size(v_a_3235_);
v___x_3240_ = lean_nat_dec_eq(v___x_3239_, v___x_3231_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_del_object(v___x_3237_);
v___x_3241_ = lean_array_to_list(v_a_3235_);
v___x_3242_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2);
v___x_3243_ = l_Lean_MessageData_joinSep(v___x_3241_, v___x_3242_);
v___x_3244_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3245_ = l_Lean_MessageData_ofExpr(v_c_3219_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v___x_3243_);
v___x_3250_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3251_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_dec(v_a_3235_);
lean_dec_ref(v_c_3219_);
v___x_3253_ = lean_box(0);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3253_);
v___x_3255_ = v___x_3237_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_c_3219_);
v_a_3258_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3234_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3234_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v_args_3220_);
lean_dec_ref(v_c_3219_);
v_a_3266_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3229_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3229_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v_c_3274_, lean_object* v_args_3275_, lean_object* v_ty_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v_c_3274_, v_args_3275_, v_ty_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_ty_3276_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_c_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3289_; 
lean_inc(v_a_3287_);
lean_inc_ref(v_a_3286_);
lean_inc(v_a_3285_);
lean_inc_ref(v_a_3284_);
lean_inc_ref(v_c_3283_);
v___x_3289_ = lean_infer_type(v_c_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___f_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref(v___x_3289_);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3291_, 0, v_c_3283_);
v___x_3292_ = 0;
v___x_3293_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3290_, v___f_3291_, v___x_3292_, v___x_3292_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v_c_3283_);
v_a_3294_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3289_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3289_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_c_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Meta_checkImpossibleInstance(v_c_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
return v_res_3308_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_declName_3318_, lean_object* v_x_3319_, lean_object* v_target_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
lean_inc_ref(v_target_3320_);
v___x_3326_ = l_Lean_Meta_isClass_x3f(v_target_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3350_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3350_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3350_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
if (lean_obj_tag(v_a_3327_) == 0)
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Lean_Expr_isSorry(v_target_3320_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_del_object(v___x_3329_);
v___x_3332_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3333_ = l_Lean_MessageData_ofName(v_declName_3318_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_MessageData_ofExpr(v_target_3320_);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3340_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec_ref(v_target_3320_);
lean_dec(v_declName_3318_);
v___x_3342_ = lean_box(0);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3342_);
v___x_3344_ = v___x_3329_;
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
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_dec_ref(v_a_3327_);
lean_dec_ref(v_target_3320_);
lean_dec(v_declName_3318_);
v___x_3346_ = lean_box(0);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3346_);
v___x_3348_ = v___x_3329_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref(v_target_3320_);
lean_dec(v_declName_3318_);
v_a_3351_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3326_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3326_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_declName_3359_, lean_object* v_x_3360_, lean_object* v_target_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_declName_3359_, v_x_3360_, v_target_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec_ref(v_x_3360_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_declName_3368_, lean_object* v_c_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3375_; 
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
v___x_3375_ = lean_infer_type(v_c_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___f_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref(v___x_3375_);
v___f_3377_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3377_, 0, v_declName_3368_);
v___x_3378_ = 0;
v___x_3379_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3376_, v___f_3377_, v___x_3378_, v___x_3378_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
return v___x_3379_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec(v_declName_3368_);
v_a_3380_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3375_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3375_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_declName_3388_, lean_object* v_c_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Meta_checkNonClassInstance(v_declName_3388_, v_c_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v_env_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_st_ref_get(v___y_3397_);
v_env_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc_ref(v_env_3400_);
lean_dec(v___x_3399_);
v___x_3401_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3400_, v_declName_3396_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3403_, v___y_3404_);
lean_dec(v___y_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3407_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3420_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3427_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
lean_ctor_set(v___x_3427_, 2, v___x_3426_);
lean_ctor_set(v___x_3427_, 3, v___x_3426_);
lean_ctor_set(v___x_3427_, 4, v___x_3426_);
lean_ctor_set(v___x_3427_, 5, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3428_, lean_object* v_b_3429_, uint8_t v_kind_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_currNamespace_3435_; lean_object* v___x_3436_; lean_object* v_env_3437_; lean_object* v_nextMacroScope_3438_; lean_object* v_ngen_3439_; lean_object* v_auxDeclNGen_3440_; lean_object* v_traceState_3441_; lean_object* v_messages_3442_; lean_object* v_infoState_3443_; lean_object* v_snapshotTasks_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3471_; 
v_currNamespace_3435_ = lean_ctor_get(v___y_3432_, 6);
v___x_3436_ = lean_st_ref_take(v___y_3433_);
v_env_3437_ = lean_ctor_get(v___x_3436_, 0);
v_nextMacroScope_3438_ = lean_ctor_get(v___x_3436_, 1);
v_ngen_3439_ = lean_ctor_get(v___x_3436_, 2);
v_auxDeclNGen_3440_ = lean_ctor_get(v___x_3436_, 3);
v_traceState_3441_ = lean_ctor_get(v___x_3436_, 4);
v_messages_3442_ = lean_ctor_get(v___x_3436_, 6);
v_infoState_3443_ = lean_ctor_get(v___x_3436_, 7);
v_snapshotTasks_3444_ = lean_ctor_get(v___x_3436_, 8);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3436_, 5);
lean_dec(v_unused_3472_);
v___x_3446_ = v___x_3436_;
v_isShared_3447_ = v_isSharedCheck_3471_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snapshotTasks_3444_);
lean_inc(v_infoState_3443_);
lean_inc(v_messages_3442_);
lean_inc(v_traceState_3441_);
lean_inc(v_auxDeclNGen_3440_);
lean_inc(v_ngen_3439_);
lean_inc(v_nextMacroScope_3438_);
lean_inc(v_env_3437_);
lean_dec(v___x_3436_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3471_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_inc(v_currNamespace_3435_);
v___x_3448_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3437_, v_ext_3428_, v_b_3429_, v_kind_3430_, v_currNamespace_3435_);
v___x_3449_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 5, v___x_3449_);
lean_ctor_set(v___x_3446_, 0, v___x_3448_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_nextMacroScope_3438_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_ngen_3439_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_auxDeclNGen_3440_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_traceState_3441_);
lean_ctor_set(v_reuseFailAlloc_3470_, 5, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3470_, 6, v_messages_3442_);
lean_ctor_set(v_reuseFailAlloc_3470_, 7, v_infoState_3443_);
lean_ctor_set(v_reuseFailAlloc_3470_, 8, v_snapshotTasks_3444_);
v___x_3451_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v_mctx_3454_; lean_object* v_zetaDeltaFVarIds_3455_; lean_object* v_postponed_3456_; lean_object* v_diag_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3468_; 
v___x_3452_ = lean_st_ref_set(v___y_3433_, v___x_3451_);
v___x_3453_ = lean_st_ref_take(v___y_3431_);
v_mctx_3454_ = lean_ctor_get(v___x_3453_, 0);
v_zetaDeltaFVarIds_3455_ = lean_ctor_get(v___x_3453_, 2);
v_postponed_3456_ = lean_ctor_get(v___x_3453_, 3);
v_diag_3457_ = lean_ctor_get(v___x_3453_, 4);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3453_, 1);
lean_dec(v_unused_3469_);
v___x_3459_ = v___x_3453_;
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_diag_3457_);
lean_inc(v_postponed_3456_);
lean_inc(v_zetaDeltaFVarIds_3455_);
lean_inc(v_mctx_3454_);
lean_dec(v___x_3453_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3461_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_mctx_3454_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_zetaDeltaFVarIds_3455_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_postponed_3456_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_diag_3457_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_st_ref_set(v___y_3431_, v___x_3463_);
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
return v___x_3466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3473_, lean_object* v_b_3474_, lean_object* v_kind_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v_kind_boxed_3480_; lean_object* v_res_3481_; 
v_kind_boxed_3480_ = lean_unbox(v_kind_3475_);
v_res_3481_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3473_, v_b_3474_, v_kind_boxed_3480_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3482_, lean_object* v_00_u03b2_3483_, lean_object* v_00_u03c3_3484_, lean_object* v_ext_3485_, lean_object* v_b_3486_, uint8_t v_kind_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3485_, v_b_3486_, v_kind_3487_, v___y_3489_, v___y_3490_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_00_u03b2_3495_, lean_object* v_00_u03c3_3496_, lean_object* v_ext_3497_, lean_object* v_b_3498_, lean_object* v_kind_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v_kind_boxed_3505_; lean_object* v_res_3506_; 
v_kind_boxed_3505_ = lean_unbox(v_kind_3499_);
v_res_3506_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3494_, v_00_u03b2_3495_, v_00_u03c3_3496_, v_ext_3497_, v_b_3498_, v_kind_boxed_3505_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; lean_object* v_env_3511_; uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3510_ = lean_st_ref_get(v___y_3508_);
v_env_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc_ref(v_env_3511_);
lean_dec(v___x_3510_);
v___x_3512_ = lean_get_reducibility_status(v_env_3511_, v_declName_3507_);
v___x_3513_ = lean_box(v___x_3512_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3515_, v___y_3516_);
lean_dec(v___y_3516_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3519_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
return v_res_3532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
lean_ctor_set(v___x_3538_, 2, v___x_3537_);
lean_ctor_set(v___x_3538_, 3, v___x_3537_);
lean_ctor_set(v___x_3538_, 4, v___x_3536_);
lean_ctor_set(v___x_3538_, 5, v___x_3536_);
lean_ctor_set(v___x_3538_, 6, v___x_3536_);
lean_ctor_set(v___x_3538_, 7, v___x_3536_);
lean_ctor_set(v___x_3538_, 8, v___x_3536_);
lean_ctor_set(v___x_3538_, 9, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_unsigned_to_nat(32u);
v___x_3540_ = lean_mk_empty_array_with_capacity(v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3542_ = ((size_t)5ULL);
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_unsigned_to_nat(32u);
v___x_3545_ = lean_mk_empty_array_with_capacity(v___x_3544_);
v___x_3546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3547_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
lean_ctor_set(v___x_3547_, 2, v___x_3543_);
lean_ctor_set(v___x_3547_, 3, v___x_3543_);
lean_ctor_set_usize(v___x_3547_, 4, v___x_3542_);
return v___x_3547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3548_ = lean_box(1);
v___x_3549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___x_3549_);
lean_ctor_set(v___x_3551_, 2, v___x_3548_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3569_ = l_Lean_stringToMessageData(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3573_, lean_object* v_declHint_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; lean_object* v_env_3578_; uint8_t v___x_3579_; 
v___x_3577_ = lean_st_ref_get(v___y_3575_);
v_env_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc_ref(v_env_3578_);
lean_dec(v___x_3577_);
v___x_3579_ = l_Lean_Name_isAnonymous(v_declHint_3574_);
if (v___x_3579_ == 0)
{
uint8_t v_isExporting_3580_; 
v_isExporting_3580_ = lean_ctor_get_uint8(v_env_3578_, sizeof(void*)*8);
if (v_isExporting_3580_ == 0)
{
lean_object* v___x_3581_; 
lean_dec_ref(v_env_3578_);
lean_dec(v_declHint_3574_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v_msg_3573_);
return v___x_3581_;
}
else
{
lean_object* v___x_3582_; uint8_t v___x_3583_; 
lean_inc_ref(v_env_3578_);
v___x_3582_ = l_Lean_Environment_setExporting(v_env_3578_, v___x_3579_);
lean_inc(v_declHint_3574_);
lean_inc_ref(v___x_3582_);
v___x_3583_ = l_Lean_Environment_contains(v___x_3582_, v_declHint_3574_, v_isExporting_3580_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_env_3578_);
lean_dec(v_declHint_3574_);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_msg_3573_);
return v___x_3584_;
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_c_3590_; lean_object* v___x_3591_; 
v___x_3585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3587_ = l_Lean_Options_empty;
v___x_3588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3582_);
lean_ctor_set(v___x_3588_, 1, v___x_3585_);
lean_ctor_set(v___x_3588_, 2, v___x_3586_);
lean_ctor_set(v___x_3588_, 3, v___x_3587_);
lean_inc(v_declHint_3574_);
v___x_3589_ = l_Lean_MessageData_ofConstName(v_declHint_3574_, v___x_3579_);
v_c_3590_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3590_, 0, v___x_3588_);
lean_ctor_set(v_c_3590_, 1, v___x_3589_);
v___x_3591_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3578_, v_declHint_3574_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec_ref(v_env_3578_);
lean_dec(v_declHint_3574_);
v___x_3592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v_c_3590_);
v___x_3594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3593_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = l_Lean_MessageData_note(v___x_3595_);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_msg_3573_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
return v___x_3598_;
}
else
{
lean_object* v_val_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3634_; 
v_val_3599_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3601_ = v___x_3591_;
v_isShared_3602_ = v_isSharedCheck_3634_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_val_3599_);
lean_dec(v___x_3591_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3634_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_mod_3606_; uint8_t v___x_3607_; 
v___x_3603_ = lean_box(0);
v___x_3604_ = l_Lean_Environment_header(v_env_3578_);
lean_dec_ref(v_env_3578_);
v___x_3605_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3604_);
v_mod_3606_ = lean_array_get(v___x_3603_, v___x_3605_, v_val_3599_);
lean_dec(v_val_3599_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = l_Lean_isPrivateName(v_declHint_3574_);
lean_dec(v_declHint_3574_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v_c_3590_);
v___x_3610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Lean_MessageData_ofName(v_mod_3606_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_MessageData_note(v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v_msg_3573_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3617_);
v___x_3619_ = v___x_3601_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v_c_3590_);
v___x_3623_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_MessageData_ofName(v_mod_3606_);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = l_Lean_MessageData_note(v___x_3628_);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v_msg_3573_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3630_);
v___x_3632_ = v___x_3601_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3635_; 
lean_dec_ref(v_env_3578_);
lean_dec(v_declHint_3574_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_msg_3573_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3636_, lean_object* v_declHint_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3636_, v_declHint_3637_, v___y_3638_);
lean_dec(v___y_3638_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3641_, lean_object* v_declHint_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3658_; 
v___x_3648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3641_, v_declHint_3642_, v___y_3646_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3653_ = l_Lean_unknownIdentifierMessageTag;
v___x_3654_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_a_3649_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3654_);
v___x_3656_ = v___x_3651_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3659_, lean_object* v_declHint_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3659_, v_declHint_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3667_, lean_object* v_msg_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_fileName_3674_; lean_object* v_fileMap_3675_; lean_object* v_options_3676_; lean_object* v_currRecDepth_3677_; lean_object* v_maxRecDepth_3678_; lean_object* v_ref_3679_; lean_object* v_currNamespace_3680_; lean_object* v_openDecls_3681_; lean_object* v_initHeartbeats_3682_; lean_object* v_maxHeartbeats_3683_; lean_object* v_quotContext_3684_; lean_object* v_currMacroScope_3685_; uint8_t v_diag_3686_; lean_object* v_cancelTk_x3f_3687_; uint8_t v_suppressElabErrors_3688_; lean_object* v_inheritedTraceOptions_3689_; lean_object* v_ref_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_fileName_3674_ = lean_ctor_get(v___y_3671_, 0);
v_fileMap_3675_ = lean_ctor_get(v___y_3671_, 1);
v_options_3676_ = lean_ctor_get(v___y_3671_, 2);
v_currRecDepth_3677_ = lean_ctor_get(v___y_3671_, 3);
v_maxRecDepth_3678_ = lean_ctor_get(v___y_3671_, 4);
v_ref_3679_ = lean_ctor_get(v___y_3671_, 5);
v_currNamespace_3680_ = lean_ctor_get(v___y_3671_, 6);
v_openDecls_3681_ = lean_ctor_get(v___y_3671_, 7);
v_initHeartbeats_3682_ = lean_ctor_get(v___y_3671_, 8);
v_maxHeartbeats_3683_ = lean_ctor_get(v___y_3671_, 9);
v_quotContext_3684_ = lean_ctor_get(v___y_3671_, 10);
v_currMacroScope_3685_ = lean_ctor_get(v___y_3671_, 11);
v_diag_3686_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*14);
v_cancelTk_x3f_3687_ = lean_ctor_get(v___y_3671_, 12);
v_suppressElabErrors_3688_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3689_ = lean_ctor_get(v___y_3671_, 13);
v_ref_3690_ = l_Lean_replaceRef(v_ref_3667_, v_ref_3679_);
lean_inc_ref(v_inheritedTraceOptions_3689_);
lean_inc(v_cancelTk_x3f_3687_);
lean_inc(v_currMacroScope_3685_);
lean_inc(v_quotContext_3684_);
lean_inc(v_maxHeartbeats_3683_);
lean_inc(v_initHeartbeats_3682_);
lean_inc(v_openDecls_3681_);
lean_inc(v_currNamespace_3680_);
lean_inc(v_maxRecDepth_3678_);
lean_inc(v_currRecDepth_3677_);
lean_inc_ref(v_options_3676_);
lean_inc_ref(v_fileMap_3675_);
lean_inc_ref(v_fileName_3674_);
v___x_3691_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3691_, 0, v_fileName_3674_);
lean_ctor_set(v___x_3691_, 1, v_fileMap_3675_);
lean_ctor_set(v___x_3691_, 2, v_options_3676_);
lean_ctor_set(v___x_3691_, 3, v_currRecDepth_3677_);
lean_ctor_set(v___x_3691_, 4, v_maxRecDepth_3678_);
lean_ctor_set(v___x_3691_, 5, v_ref_3690_);
lean_ctor_set(v___x_3691_, 6, v_currNamespace_3680_);
lean_ctor_set(v___x_3691_, 7, v_openDecls_3681_);
lean_ctor_set(v___x_3691_, 8, v_initHeartbeats_3682_);
lean_ctor_set(v___x_3691_, 9, v_maxHeartbeats_3683_);
lean_ctor_set(v___x_3691_, 10, v_quotContext_3684_);
lean_ctor_set(v___x_3691_, 11, v_currMacroScope_3685_);
lean_ctor_set(v___x_3691_, 12, v_cancelTk_x3f_3687_);
lean_ctor_set(v___x_3691_, 13, v_inheritedTraceOptions_3689_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*14, v_diag_3686_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*14 + 1, v_suppressElabErrors_3688_);
v___x_3692_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3668_, v___y_3669_, v___y_3670_, v___x_3691_, v___y_3672_);
lean_dec_ref(v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3693_, lean_object* v_msg_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3693_, v_msg_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v_ref_3693_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3701_, lean_object* v_msg_3702_, lean_object* v_declHint_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; lean_object* v_a_3710_; lean_object* v___x_3711_; 
v___x_3709_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3702_, v_declHint_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3701_, v_a_3710_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3712_, lean_object* v_msg_3713_, lean_object* v_declHint_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3712_, v_msg_3713_, v_declHint_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v_ref_3712_);
return v_res_3720_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3724_, lean_object* v_constName_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3731_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3732_ = 0;
lean_inc(v_constName_3725_);
v___x_3733_ = l_Lean_MessageData_ofConstName(v_constName_3725_, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3731_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3724_, v___x_3736_, v_constName_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3738_, lean_object* v_constName_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3738_, v_constName_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v_ref_3738_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_ref_3752_; lean_object* v___x_3753_; 
v_ref_3752_ = lean_ctor_get(v___y_3749_, 5);
v___x_3753_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3752_, v_constName_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; lean_object* v_env_3768_; uint8_t v___x_3769_; lean_object* v___x_3770_; 
v___x_3767_ = lean_st_ref_get(v___y_3765_);
v_env_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc_ref(v_env_3768_);
lean_dec(v___x_3767_);
v___x_3769_ = 0;
lean_inc(v_constName_3761_);
v___x_3770_ = l_Lean_Environment_find_x3f(v_env_3768_, v_constName_3761_, v___x_3769_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3771_;
}
else
{
lean_object* v_val_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v_constName_3761_);
v_val_3772_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3770_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_val_3772_);
lean_dec(v___x_3770_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set_tag(v___x_3774_, 0);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_val_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
return v_res_3786_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3794_, uint8_t v_suppressElabErrors_3795_, lean_object* v_x_3796_){
_start:
{
if (lean_obj_tag(v_x_3796_) == 1)
{
lean_object* v_pre_3797_; 
v_pre_3797_ = lean_ctor_get(v_x_3796_, 0);
switch(lean_obj_tag(v_pre_3797_))
{
case 1:
{
lean_object* v_pre_3798_; 
v_pre_3798_ = lean_ctor_get(v_pre_3797_, 0);
switch(lean_obj_tag(v_pre_3798_))
{
case 0:
{
lean_object* v_str_3799_; lean_object* v_str_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_str_3799_ = lean_ctor_get(v_x_3796_, 1);
v_str_3800_ = lean_ctor_get(v_pre_3797_, 1);
v___x_3801_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3802_ = lean_string_dec_eq(v_str_3800_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3804_ = lean_string_dec_eq(v_str_3800_, v___x_3803_);
if (v___x_3804_ == 0)
{
return v___y_3794_;
}
else
{
lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___x_3805_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3806_ = lean_string_dec_eq(v_str_3799_, v___x_3805_);
if (v___x_3806_ == 0)
{
return v___y_3794_;
}
else
{
return v_suppressElabErrors_3795_;
}
}
}
else
{
lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3807_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3808_ = lean_string_dec_eq(v_str_3799_, v___x_3807_);
if (v___x_3808_ == 0)
{
return v___y_3794_;
}
else
{
return v_suppressElabErrors_3795_;
}
}
}
case 1:
{
lean_object* v_pre_3809_; 
v_pre_3809_ = lean_ctor_get(v_pre_3798_, 0);
if (lean_obj_tag(v_pre_3809_) == 0)
{
lean_object* v_str_3810_; lean_object* v_str_3811_; lean_object* v_str_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_str_3810_ = lean_ctor_get(v_x_3796_, 1);
v_str_3811_ = lean_ctor_get(v_pre_3797_, 1);
v_str_3812_ = lean_ctor_get(v_pre_3798_, 1);
v___x_3813_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3814_ = lean_string_dec_eq(v_str_3812_, v___x_3813_);
if (v___x_3814_ == 0)
{
return v___y_3794_;
}
else
{
lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3816_ = lean_string_dec_eq(v_str_3811_, v___x_3815_);
if (v___x_3816_ == 0)
{
return v___y_3794_;
}
else
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3818_ = lean_string_dec_eq(v_str_3810_, v___x_3817_);
if (v___x_3818_ == 0)
{
return v___y_3794_;
}
else
{
return v_suppressElabErrors_3795_;
}
}
}
}
else
{
return v___y_3794_;
}
}
default: 
{
return v___y_3794_;
}
}
}
case 0:
{
lean_object* v_str_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_str_3819_ = lean_ctor_get(v_x_3796_, 1);
v___x_3820_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3821_ = lean_string_dec_eq(v_str_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
return v___y_3794_;
}
else
{
return v_suppressElabErrors_3795_;
}
}
default: 
{
return v___y_3794_;
}
}
}
else
{
return v___y_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3822_, lean_object* v_suppressElabErrors_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v___y_8828__boxed_3825_; uint8_t v_suppressElabErrors_boxed_3826_; uint8_t v_res_3827_; lean_object* v_r_3828_; 
v___y_8828__boxed_3825_ = lean_unbox(v___y_3822_);
v_suppressElabErrors_boxed_3826_ = lean_unbox(v_suppressElabErrors_3823_);
v_res_3827_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8828__boxed_3825_, v_suppressElabErrors_boxed_3826_, v_x_3824_);
lean_dec(v_x_3824_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3829_, lean_object* v_msgData_3830_, uint8_t v_severity_3831_, uint8_t v_isSilent_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___y_3839_; lean_object* v___y_3840_; uint8_t v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; uint8_t v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3875_; uint8_t v___y_3876_; uint8_t v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; uint8_t v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3900_; uint8_t v___y_3901_; uint8_t v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; uint8_t v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3911_; uint8_t v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; uint8_t v___y_3916_; uint8_t v___y_3917_; uint8_t v___x_3922_; uint8_t v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; uint8_t v___y_3929_; uint8_t v___y_3930_; uint8_t v___y_3932_; uint8_t v___x_3947_; 
v___x_3922_ = 2;
v___x_3947_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3831_, v___x_3922_);
if (v___x_3947_ == 0)
{
v___y_3932_ = v___x_3947_;
goto v___jp_3931_;
}
else
{
uint8_t v___x_3948_; 
lean_inc_ref(v_msgData_3830_);
v___x_3948_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3830_);
v___y_3932_ = v___x_3948_;
goto v___jp_3931_;
}
v___jp_3838_:
{
lean_object* v___x_3848_; lean_object* v_currNamespace_3849_; lean_object* v_openDecls_3850_; lean_object* v_env_3851_; lean_object* v_nextMacroScope_3852_; lean_object* v_ngen_3853_; lean_object* v_auxDeclNGen_3854_; lean_object* v_traceState_3855_; lean_object* v_cache_3856_; lean_object* v_messages_3857_; lean_object* v_infoState_3858_; lean_object* v_snapshotTasks_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3873_; 
v___x_3848_ = lean_st_ref_take(v___y_3847_);
v_currNamespace_3849_ = lean_ctor_get(v___y_3846_, 6);
v_openDecls_3850_ = lean_ctor_get(v___y_3846_, 7);
v_env_3851_ = lean_ctor_get(v___x_3848_, 0);
v_nextMacroScope_3852_ = lean_ctor_get(v___x_3848_, 1);
v_ngen_3853_ = lean_ctor_get(v___x_3848_, 2);
v_auxDeclNGen_3854_ = lean_ctor_get(v___x_3848_, 3);
v_traceState_3855_ = lean_ctor_get(v___x_3848_, 4);
v_cache_3856_ = lean_ctor_get(v___x_3848_, 5);
v_messages_3857_ = lean_ctor_get(v___x_3848_, 6);
v_infoState_3858_ = lean_ctor_get(v___x_3848_, 7);
v_snapshotTasks_3859_ = lean_ctor_get(v___x_3848_, 8);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3861_ = v___x_3848_;
v_isShared_3862_ = v_isSharedCheck_3873_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_snapshotTasks_3859_);
lean_inc(v_infoState_3858_);
lean_inc(v_messages_3857_);
lean_inc(v_cache_3856_);
lean_inc(v_traceState_3855_);
lean_inc(v_auxDeclNGen_3854_);
lean_inc(v_ngen_3853_);
lean_inc(v_nextMacroScope_3852_);
lean_inc(v_env_3851_);
lean_dec(v___x_3848_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3873_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
lean_inc(v_openDecls_3850_);
lean_inc(v_currNamespace_3849_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v_currNamespace_3849_);
lean_ctor_set(v___x_3863_, 1, v_openDecls_3850_);
v___x_3864_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___y_3842_);
lean_inc_ref(v___y_3840_);
lean_inc_ref(v___y_3844_);
v___x_3865_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3865_, 0, v___y_3844_);
lean_ctor_set(v___x_3865_, 1, v___y_3843_);
lean_ctor_set(v___x_3865_, 2, v___y_3839_);
lean_ctor_set(v___x_3865_, 3, v___y_3840_);
lean_ctor_set(v___x_3865_, 4, v___x_3864_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*5, v___y_3845_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*5 + 1, v___y_3841_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*5 + 2, v_isSilent_3832_);
v___x_3866_ = l_Lean_MessageLog_add(v___x_3865_, v_messages_3857_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 6, v___x_3866_);
v___x_3868_ = v___x_3861_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_env_3851_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_nextMacroScope_3852_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_ngen_3853_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_auxDeclNGen_3854_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_traceState_3855_);
lean_ctor_set(v_reuseFailAlloc_3872_, 5, v_cache_3856_);
lean_ctor_set(v_reuseFailAlloc_3872_, 6, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3872_, 7, v_infoState_3858_);
lean_ctor_set(v_reuseFailAlloc_3872_, 8, v_snapshotTasks_3859_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = lean_st_ref_set(v___y_3847_, v___x_3868_);
v___x_3870_ = lean_box(0);
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
}
}
v___jp_3874_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3898_; 
v___x_3883_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3830_);
v___x_3884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3883_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3898_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3898_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
lean_inc_ref_n(v___y_3878_, 2);
v___x_3889_ = l_Lean_FileMap_toPosition(v___y_3878_, v___y_3879_);
lean_dec(v___y_3879_);
v___x_3890_ = l_Lean_FileMap_toPosition(v___y_3878_, v___y_3882_);
lean_dec(v___y_3882_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
v___x_3892_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3876_ == 0)
{
lean_del_object(v___x_3887_);
lean_dec_ref(v___y_3875_);
v___y_3839_ = v___x_3891_;
v___y_3840_ = v___x_3892_;
v___y_3841_ = v___y_3877_;
v___y_3842_ = v_a_3885_;
v___y_3843_ = v___x_3889_;
v___y_3844_ = v___y_3880_;
v___y_3845_ = v___y_3881_;
v___y_3846_ = v___y_3835_;
v___y_3847_ = v___y_3836_;
goto v___jp_3838_;
}
else
{
uint8_t v___x_3893_; 
lean_inc(v_a_3885_);
v___x_3893_ = l_Lean_MessageData_hasTag(v___y_3875_, v_a_3885_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_dec_ref(v___x_3891_);
lean_dec_ref(v___x_3889_);
lean_dec(v_a_3885_);
v___x_3894_ = lean_box(0);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3894_);
v___x_3896_ = v___x_3887_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
else
{
lean_del_object(v___x_3887_);
v___y_3839_ = v___x_3891_;
v___y_3840_ = v___x_3892_;
v___y_3841_ = v___y_3877_;
v___y_3842_ = v_a_3885_;
v___y_3843_ = v___x_3889_;
v___y_3844_ = v___y_3880_;
v___y_3845_ = v___y_3881_;
v___y_3846_ = v___y_3835_;
v___y_3847_ = v___y_3836_;
goto v___jp_3838_;
}
}
}
}
v___jp_3899_:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_Syntax_getTailPos_x3f(v___y_3903_, v___y_3906_);
lean_dec(v___y_3903_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_inc(v___y_3907_);
v___y_3875_ = v___y_3900_;
v___y_3876_ = v___y_3901_;
v___y_3877_ = v___y_3902_;
v___y_3878_ = v___y_3904_;
v___y_3879_ = v___y_3907_;
v___y_3880_ = v___y_3905_;
v___y_3881_ = v___y_3906_;
v___y_3882_ = v___y_3907_;
goto v___jp_3874_;
}
else
{
lean_object* v_val_3909_; 
v_val_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3909_);
lean_dec_ref(v___x_3908_);
v___y_3875_ = v___y_3900_;
v___y_3876_ = v___y_3901_;
v___y_3877_ = v___y_3902_;
v___y_3878_ = v___y_3904_;
v___y_3879_ = v___y_3907_;
v___y_3880_ = v___y_3905_;
v___y_3881_ = v___y_3906_;
v___y_3882_ = v_val_3909_;
goto v___jp_3874_;
}
}
v___jp_3910_:
{
lean_object* v_ref_3918_; lean_object* v___x_3919_; 
v_ref_3918_ = l_Lean_replaceRef(v_ref_3829_, v___y_3914_);
v___x_3919_ = l_Lean_Syntax_getPos_x3f(v_ref_3918_, v___y_3916_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_unsigned_to_nat(0u);
v___y_3900_ = v___y_3911_;
v___y_3901_ = v___y_3912_;
v___y_3902_ = v___y_3917_;
v___y_3903_ = v_ref_3918_;
v___y_3904_ = v___y_3913_;
v___y_3905_ = v___y_3915_;
v___y_3906_ = v___y_3916_;
v___y_3907_ = v___x_3920_;
goto v___jp_3899_;
}
else
{
lean_object* v_val_3921_; 
v_val_3921_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_val_3921_);
lean_dec_ref(v___x_3919_);
v___y_3900_ = v___y_3911_;
v___y_3901_ = v___y_3912_;
v___y_3902_ = v___y_3917_;
v___y_3903_ = v_ref_3918_;
v___y_3904_ = v___y_3913_;
v___y_3905_ = v___y_3915_;
v___y_3906_ = v___y_3916_;
v___y_3907_ = v_val_3921_;
goto v___jp_3899_;
}
}
v___jp_3923_:
{
if (v___y_3930_ == 0)
{
v___y_3911_ = v___y_3925_;
v___y_3912_ = v___y_3924_;
v___y_3913_ = v___y_3927_;
v___y_3914_ = v___y_3926_;
v___y_3915_ = v___y_3928_;
v___y_3916_ = v___y_3929_;
v___y_3917_ = v_severity_3831_;
goto v___jp_3910_;
}
else
{
v___y_3911_ = v___y_3925_;
v___y_3912_ = v___y_3924_;
v___y_3913_ = v___y_3927_;
v___y_3914_ = v___y_3926_;
v___y_3915_ = v___y_3928_;
v___y_3916_ = v___y_3929_;
v___y_3917_ = v___x_3922_;
goto v___jp_3910_;
}
}
v___jp_3931_:
{
if (v___y_3932_ == 0)
{
lean_object* v_fileName_3933_; lean_object* v_fileMap_3934_; lean_object* v_options_3935_; lean_object* v_ref_3936_; uint8_t v_suppressElabErrors_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___f_3940_; uint8_t v___x_3941_; uint8_t v___x_3942_; 
v_fileName_3933_ = lean_ctor_get(v___y_3835_, 0);
v_fileMap_3934_ = lean_ctor_get(v___y_3835_, 1);
v_options_3935_ = lean_ctor_get(v___y_3835_, 2);
v_ref_3936_ = lean_ctor_get(v___y_3835_, 5);
v_suppressElabErrors_3937_ = lean_ctor_get_uint8(v___y_3835_, sizeof(void*)*14 + 1);
v___x_3938_ = lean_box(v___y_3932_);
v___x_3939_ = lean_box(v_suppressElabErrors_3937_);
v___f_3940_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3940_, 0, v___x_3938_);
lean_closure_set(v___f_3940_, 1, v___x_3939_);
v___x_3941_ = 1;
v___x_3942_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3831_, v___x_3941_);
if (v___x_3942_ == 0)
{
v___y_3924_ = v_suppressElabErrors_3937_;
v___y_3925_ = v___f_3940_;
v___y_3926_ = v_ref_3936_;
v___y_3927_ = v_fileMap_3934_;
v___y_3928_ = v_fileName_3933_;
v___y_3929_ = v___y_3932_;
v___y_3930_ = v___x_3942_;
goto v___jp_3923_;
}
else
{
lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3943_ = l_Lean_warningAsError;
v___x_3944_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3935_, v___x_3943_);
v___y_3924_ = v_suppressElabErrors_3937_;
v___y_3925_ = v___f_3940_;
v___y_3926_ = v_ref_3936_;
v___y_3927_ = v_fileMap_3934_;
v___y_3928_ = v_fileName_3933_;
v___y_3929_ = v___y_3932_;
v___y_3930_ = v___x_3944_;
goto v___jp_3923_;
}
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec_ref(v_msgData_3830_);
v___x_3945_ = lean_box(0);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3949_, lean_object* v_msgData_3950_, lean_object* v_severity_3951_, lean_object* v_isSilent_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v_severity_boxed_3958_; uint8_t v_isSilent_boxed_3959_; lean_object* v_res_3960_; 
v_severity_boxed_3958_ = lean_unbox(v_severity_3951_);
v_isSilent_boxed_3959_ = lean_unbox(v_isSilent_3952_);
v_res_3960_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3949_, v_msgData_3950_, v_severity_boxed_3958_, v_isSilent_boxed_3959_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v_ref_3949_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3961_, uint8_t v_severity_3962_, uint8_t v_isSilent_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_ref_3969_; lean_object* v___x_3970_; 
v_ref_3969_ = lean_ctor_get(v___y_3966_, 5);
v___x_3970_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3969_, v_msgData_3961_, v_severity_3962_, v_isSilent_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3971_, lean_object* v_severity_3972_, lean_object* v_isSilent_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
uint8_t v_severity_boxed_3979_; uint8_t v_isSilent_boxed_3980_; lean_object* v_res_3981_; 
v_severity_boxed_3979_ = lean_unbox(v_severity_3972_);
v_isSilent_boxed_3980_ = lean_unbox(v_isSilent_3973_);
v_res_3981_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3971_, v_severity_boxed_3979_, v_isSilent_boxed_3980_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; 
v___x_3988_ = 1;
v___x_3989_ = 0;
v___x_3990_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3982_, v___x_3988_, v___x_3989_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; lean_object* v_env_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4004_ = lean_st_ref_get(v___y_4002_);
v_env_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc_ref(v_env_4005_);
lean_dec(v___x_4004_);
v___x_4006_ = 0;
lean_inc(v_constName_3998_);
v___x_4007_ = l_Lean_Environment_findConstVal_x3f(v_env_4005_, v_constName_3998_, v___x_4006_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4008_;
}
else
{
lean_object* v_val_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_constName_3998_);
v_val_4009_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4007_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_val_4009_);
lean_dec(v___x_4007_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set_tag(v___x_4011_, 0);
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_val_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
if (lean_obj_tag(v_a_4024_) == 0)
{
lean_object* v___x_4026_; 
v___x_4026_ = l_List_reverse___redArg(v_a_4025_);
return v___x_4026_;
}
else
{
lean_object* v_head_4027_; lean_object* v_tail_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4037_; 
v_head_4027_ = lean_ctor_get(v_a_4024_, 0);
v_tail_4028_ = lean_ctor_get(v_a_4024_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_4024_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4030_ = v_a_4024_;
v_isShared_4031_ = v_isSharedCheck_4037_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_tail_4028_);
lean_inc(v_head_4027_);
lean_dec(v_a_4024_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4037_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4032_ = l_Lean_mkLevelParam(v_head_4027_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v_a_4025_);
lean_ctor_set(v___x_4030_, 0, v___x_4032_);
v___x_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_a_4025_);
v___x_4034_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
v_a_4024_ = v_tail_4028_;
v_a_4025_ = v___x_4034_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; 
lean_inc(v_constName_4038_);
v___x_4044_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4056_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4056_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4056_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v_levelParams_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v_levelParams_4049_ = lean_ctor_get(v_a_4045_, 1);
lean_inc(v_levelParams_4049_);
lean_dec(v_a_4045_);
v___x_4050_ = lean_box(0);
v___x_4051_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4049_, v___x_4050_);
v___x_4052_ = l_Lean_mkConst(v_constName_4038_, v___x_4051_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4052_);
v___x_4054_ = v___x_4047_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_constName_4038_);
v_a_4057_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4044_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4044_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4071_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4074_ = l_Lean_stringToMessageData(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4077_ = l_Lean_stringToMessageData(v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4078_, uint8_t v_attrKind_4079_, lean_object* v_prio_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; 
lean_inc(v_declName_4078_);
v___x_4086_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4078_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc_n(v_a_4087_, 2);
lean_dec_ref(v___x_4086_);
v___x_4088_ = l_Lean_Meta_checkImpossibleInstance(v_a_4087_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v___x_4089_; 
lean_dec_ref(v___x_4088_);
lean_inc(v_a_4087_);
lean_inc(v_declName_4078_);
v___x_4089_ = l_Lean_Meta_checkNonClassInstance(v_declName_4078_, v_a_4087_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v___x_4089_);
lean_inc(v_a_4087_);
v___x_4090_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4087_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___x_4119_; lean_object* v_a_4120_; uint8_t v___x_4121_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref(v___x_4090_);
lean_inc(v_declName_4078_);
v___x_4119_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4078_, v_a_4084_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
v___x_4121_ = lean_unbox(v_a_4120_);
lean_dec(v_a_4120_);
switch(v___x_4121_)
{
case 0:
{
v___y_4093_ = v_a_4081_;
v___y_4094_ = v_a_4082_;
v___y_4095_ = v_a_4083_;
v___y_4096_ = v_a_4084_;
goto v___jp_4092_;
}
case 3:
{
v___y_4093_ = v_a_4081_;
v___y_4094_ = v_a_4082_;
v___y_4095_ = v_a_4083_;
v___y_4096_ = v_a_4084_;
goto v___jp_4092_;
}
default: 
{
lean_object* v___x_4122_; 
lean_inc(v_declName_4078_);
v___x_4122_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4078_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; uint8_t v___x_4124_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = l_Lean_ConstantInfo_isDefinition(v_a_4123_);
lean_dec(v_a_4123_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v_env_4126_; uint8_t v___x_4127_; 
v___x_4125_ = lean_st_ref_get(v_a_4084_);
v_env_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc_ref(v_env_4126_);
lean_dec(v___x_4125_);
lean_inc(v_declName_4078_);
v___x_4127_ = l_Lean_wasOriginallyDefn(v_env_4126_, v_declName_4078_);
if (v___x_4127_ == 0)
{
v___y_4093_ = v_a_4081_;
v___y_4094_ = v_a_4082_;
v___y_4095_ = v_a_4083_;
v___y_4096_ = v_a_4084_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4128_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
lean_inc(v_declName_4078_);
v___x_4129_ = l_Lean_MessageData_ofName(v_declName_4078_);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_4132_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_dec_ref(v___x_4133_);
v___y_4093_ = v_a_4081_;
v___y_4094_ = v_a_4082_;
v___y_4095_ = v_a_4083_;
v___y_4096_ = v_a_4084_;
goto v___jp_4092_;
}
else
{
lean_dec(v_a_4091_);
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
return v___x_4133_;
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4134_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
lean_inc(v_declName_4078_);
v___x_4135_ = l_Lean_MessageData_ofName(v_declName_4078_);
v___x_4136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4134_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_4138_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_dec_ref(v___x_4139_);
v___y_4093_ = v_a_4081_;
v___y_4094_ = v_a_4082_;
v___y_4095_ = v_a_4083_;
v___y_4096_ = v_a_4084_;
goto v___jp_4092_;
}
else
{
lean_dec(v_a_4091_);
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
return v___x_4139_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_a_4091_);
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
v_a_4140_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4122_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4122_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
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
v___jp_4092_:
{
lean_object* v___x_4097_; lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4118_; 
lean_inc(v_declName_4078_);
v___x_4097_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4078_, v___y_4096_);
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4118_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4118_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; 
lean_inc(v_a_4087_);
v___x_4102_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4087_, v_a_4098_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref(v___x_4102_);
v___x_4104_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4101_ == 0)
{
lean_ctor_set_tag(v___x_4100_, 1);
lean_ctor_set(v___x_4100_, 0, v_declName_4078_);
v___x_4106_ = v___x_4100_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_declName_4078_);
v___x_4106_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4107_, 0, v_a_4091_);
lean_ctor_set(v___x_4107_, 1, v_a_4087_);
lean_ctor_set(v___x_4107_, 2, v_prio_4080_);
lean_ctor_set(v___x_4107_, 3, v___x_4106_);
lean_ctor_set(v___x_4107_, 4, v_a_4103_);
lean_ctor_set_uint8(v___x_4107_, sizeof(void*)*5, v_attrKind_4079_);
v___x_4108_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4104_, v___x_4107_, v_attrKind_4079_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4108_;
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_del_object(v___x_4100_);
lean_dec(v_a_4091_);
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
v_a_4110_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4102_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4102_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
v_a_4148_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4090_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4090_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
return v___x_4089_;
}
}
else
{
lean_dec(v_a_4087_);
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
return v___x_4088_;
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_prio_4080_);
lean_dec(v_declName_4078_);
v_a_4156_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4086_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4086_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4164_, lean_object* v_attrKind_4165_, lean_object* v_prio_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
uint8_t v_attrKind_boxed_4172_; lean_object* v_res_4173_; 
v_attrKind_boxed_4172_ = lean_unbox(v_attrKind_4165_);
v_res_4173_ = l_Lean_Meta_addInstance(v_declName_4164_, v_attrKind_boxed_4172_, v_prio_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4174_, lean_object* v_constName_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4182_, lean_object* v_constName_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4182_, v_constName_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4190_, lean_object* v_ref_4191_, lean_object* v_constName_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4191_, v_constName_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4199_, lean_object* v_ref_4200_, lean_object* v_constName_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4199_, v_ref_4200_, v_constName_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v_ref_4200_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_4208_, lean_object* v_ref_4209_, lean_object* v_msg_4210_, lean_object* v_declHint_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_4209_, v_msg_4210_, v_declHint_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4218_, lean_object* v_ref_4219_, lean_object* v_msg_4220_, lean_object* v_declHint_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_4218_, v_ref_4219_, v_msg_4220_, v_declHint_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v_ref_4219_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_4228_, lean_object* v_declHint_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_4228_, v_declHint_4229_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_4236_, lean_object* v_declHint_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_4236_, v_declHint_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_4244_, lean_object* v_ref_4245_, lean_object* v_msg_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_4245_, v_msg_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4253_, lean_object* v_ref_4254_, lean_object* v_msg_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_4253_, v_ref_4254_, v_msg_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v_ref_4254_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4262_, uint8_t v_s_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; lean_object* v_env_4268_; lean_object* v_nextMacroScope_4269_; lean_object* v_ngen_4270_; lean_object* v_auxDeclNGen_4271_; lean_object* v_traceState_4272_; lean_object* v_messages_4273_; lean_object* v_infoState_4274_; lean_object* v_snapshotTasks_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4304_; 
v___x_4267_ = lean_st_ref_take(v___y_4265_);
v_env_4268_ = lean_ctor_get(v___x_4267_, 0);
v_nextMacroScope_4269_ = lean_ctor_get(v___x_4267_, 1);
v_ngen_4270_ = lean_ctor_get(v___x_4267_, 2);
v_auxDeclNGen_4271_ = lean_ctor_get(v___x_4267_, 3);
v_traceState_4272_ = lean_ctor_get(v___x_4267_, 4);
v_messages_4273_ = lean_ctor_get(v___x_4267_, 6);
v_infoState_4274_ = lean_ctor_get(v___x_4267_, 7);
v_snapshotTasks_4275_ = lean_ctor_get(v___x_4267_, 8);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; 
v_unused_4305_ = lean_ctor_get(v___x_4267_, 5);
lean_dec(v_unused_4305_);
v___x_4277_ = v___x_4267_;
v_isShared_4278_ = v_isSharedCheck_4304_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_snapshotTasks_4275_);
lean_inc(v_infoState_4274_);
lean_inc(v_messages_4273_);
lean_inc(v_traceState_4272_);
lean_inc(v_auxDeclNGen_4271_);
lean_inc(v_ngen_4270_);
lean_inc(v_nextMacroScope_4269_);
lean_inc(v_env_4268_);
lean_dec(v___x_4267_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4304_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4279_ = 0;
v___x_4280_ = lean_box(0);
v___x_4281_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4268_, v_declName_4262_, v_s_4263_, v___x_4279_, v___x_4280_);
v___x_4282_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 5, v___x_4282_);
lean_ctor_set(v___x_4277_, 0, v___x_4281_);
v___x_4284_ = v___x_4277_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_nextMacroScope_4269_);
lean_ctor_set(v_reuseFailAlloc_4303_, 2, v_ngen_4270_);
lean_ctor_set(v_reuseFailAlloc_4303_, 3, v_auxDeclNGen_4271_);
lean_ctor_set(v_reuseFailAlloc_4303_, 4, v_traceState_4272_);
lean_ctor_set(v_reuseFailAlloc_4303_, 5, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4303_, 6, v_messages_4273_);
lean_ctor_set(v_reuseFailAlloc_4303_, 7, v_infoState_4274_);
lean_ctor_set(v_reuseFailAlloc_4303_, 8, v_snapshotTasks_4275_);
v___x_4284_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v_mctx_4287_; lean_object* v_zetaDeltaFVarIds_4288_; lean_object* v_postponed_4289_; lean_object* v_diag_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4301_; 
v___x_4285_ = lean_st_ref_set(v___y_4265_, v___x_4284_);
v___x_4286_ = lean_st_ref_take(v___y_4264_);
v_mctx_4287_ = lean_ctor_get(v___x_4286_, 0);
v_zetaDeltaFVarIds_4288_ = lean_ctor_get(v___x_4286_, 2);
v_postponed_4289_ = lean_ctor_get(v___x_4286_, 3);
v_diag_4290_ = lean_ctor_get(v___x_4286_, 4);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; 
v_unused_4302_ = lean_ctor_get(v___x_4286_, 1);
lean_dec(v_unused_4302_);
v___x_4292_ = v___x_4286_;
v_isShared_4293_ = v_isSharedCheck_4301_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_diag_4290_);
lean_inc(v_postponed_4289_);
lean_inc(v_zetaDeltaFVarIds_4288_);
lean_inc(v_mctx_4287_);
lean_dec(v___x_4286_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4301_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; lean_object* v___x_4296_; 
v___x_4294_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 1, v___x_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_mctx_4287_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4300_, 2, v_zetaDeltaFVarIds_4288_);
lean_ctor_set(v_reuseFailAlloc_4300_, 3, v_postponed_4289_);
lean_ctor_set(v_reuseFailAlloc_4300_, 4, v_diag_4290_);
v___x_4296_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_st_ref_set(v___y_4264_, v___x_4296_);
v___x_4298_ = lean_box(0);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4306_, lean_object* v_s_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v_s_boxed_4311_; lean_object* v_res_4312_; 
v_s_boxed_4311_ = lean_unbox(v_s_4307_);
v_res_4312_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4306_, v_s_boxed_4311_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec(v___y_4308_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4313_, uint8_t v_s_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4313_, v_s_4314_, v___y_4316_, v___y_4318_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4321_, lean_object* v_s_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v_s_boxed_4328_; lean_object* v_res_4329_; 
v_s_boxed_4328_ = lean_unbox(v_s_4322_);
v_res_4329_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4321_, v_s_boxed_4328_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4330_, uint8_t v_attrKind_4331_, lean_object* v_prio_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = 3;
lean_inc(v_declName_4330_);
v___x_4339_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4330_, v___x_4338_, v_a_4334_, v_a_4336_);
lean_dec_ref(v___x_4339_);
v___x_4340_ = l_Lean_Meta_addInstance(v_declName_4330_, v_attrKind_4331_, v_prio_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4341_, lean_object* v_attrKind_4342_, lean_object* v_prio_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
uint8_t v_attrKind_boxed_4349_; lean_object* v_res_4350_; 
v_attrKind_boxed_4349_ = lean_unbox(v_attrKind_4342_);
v_res_4350_ = l_Lean_Meta_registerInstance(v_declName_4341_, v_attrKind_boxed_4349_, v_prio_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4351_, lean_object* v_x_4352_){
_start:
{
lean_inc_ref(v_a_4351_);
return v_a_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4353_, lean_object* v_x_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4353_, v_x_4354_);
lean_dec_ref(v_x_4354_);
lean_dec_ref(v_a_4353_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v_env_4361_; lean_object* v_options_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4360_ = lean_st_ref_get(v___y_4358_);
v_env_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc_ref(v_env_4361_);
lean_dec(v___x_4360_);
v_options_4362_ = lean_ctor_get(v___y_4357_, 2);
v___x_4363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_4364_ = lean_unsigned_to_nat(32u);
v___x_4365_ = lean_mk_empty_array_with_capacity(v___x_4364_);
lean_dec_ref(v___x_4365_);
v___x_4366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_4362_);
v___x_4367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4367_, 0, v_env_4361_);
lean_ctor_set(v___x_4367_, 1, v___x_4363_);
lean_ctor_set(v___x_4367_, 2, v___x_4366_);
lean_ctor_set(v___x_4367_, 3, v_options_4362_);
v___x_4368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
lean_ctor_set(v___x_4368_, 1, v_msgData_4356_);
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_ref_4379_; lean_object* v___x_4380_; lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4389_; 
v_ref_4379_ = lean_ctor_get(v___y_4376_, 5);
v___x_4380_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4375_, v___y_4376_, v___y_4377_);
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4389_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4389_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4387_; 
lean_inc(v_ref_4379_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_ref_4379_);
lean_ctor_set(v___x_4385_, 1, v_a_4381_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 1);
lean_ctor_set(v___x_4383_, 0, v___x_4385_);
v___x_4387_ = v___x_4383_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4395_, lean_object* v_i_4396_, lean_object* v_k_4397_){
_start:
{
lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4398_ = lean_array_get_size(v_keys_4395_);
v___x_4399_ = lean_nat_dec_lt(v_i_4396_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_dec(v_i_4396_);
return v___x_4399_;
}
else
{
lean_object* v_k_x27_4400_; uint8_t v___x_4401_; 
v_k_x27_4400_ = lean_array_fget_borrowed(v_keys_4395_, v_i_4396_);
v___x_4401_ = lean_name_eq(v_k_4397_, v_k_x27_4400_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = lean_unsigned_to_nat(1u);
v___x_4403_ = lean_nat_add(v_i_4396_, v___x_4402_);
lean_dec(v_i_4396_);
v_i_4396_ = v___x_4403_;
goto _start;
}
else
{
lean_dec(v_i_4396_);
return v___x_4401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4405_, lean_object* v_i_4406_, lean_object* v_k_4407_){
_start:
{
uint8_t v_res_4408_; lean_object* v_r_4409_; 
v_res_4408_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4405_, v_i_4406_, v_k_4407_);
lean_dec(v_k_4407_);
lean_dec_ref(v_keys_4405_);
v_r_4409_ = lean_box(v_res_4408_);
return v_r_4409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4410_, size_t v_x_4411_, lean_object* v_x_4412_){
_start:
{
if (lean_obj_tag(v_x_4410_) == 0)
{
lean_object* v_es_4413_; lean_object* v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; size_t v___x_4417_; lean_object* v_j_4418_; lean_object* v___x_4419_; 
v_es_4413_ = lean_ctor_get(v_x_4410_, 0);
v___x_4414_ = lean_box(2);
v___x_4415_ = ((size_t)5ULL);
v___x_4416_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4417_ = lean_usize_land(v_x_4411_, v___x_4416_);
v_j_4418_ = lean_usize_to_nat(v___x_4417_);
v___x_4419_ = lean_array_get_borrowed(v___x_4414_, v_es_4413_, v_j_4418_);
lean_dec(v_j_4418_);
switch(lean_obj_tag(v___x_4419_))
{
case 0:
{
lean_object* v_key_4420_; uint8_t v___x_4421_; 
v_key_4420_ = lean_ctor_get(v___x_4419_, 0);
v___x_4421_ = lean_name_eq(v_x_4412_, v_key_4420_);
return v___x_4421_;
}
case 1:
{
lean_object* v_node_4422_; size_t v___x_4423_; 
v_node_4422_ = lean_ctor_get(v___x_4419_, 0);
v___x_4423_ = lean_usize_shift_right(v_x_4411_, v___x_4415_);
v_x_4410_ = v_node_4422_;
v_x_4411_ = v___x_4423_;
goto _start;
}
default: 
{
uint8_t v___x_4425_; 
v___x_4425_ = 0;
return v___x_4425_;
}
}
}
else
{
lean_object* v_ks_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v_ks_4426_ = lean_ctor_get(v_x_4410_, 0);
v___x_4427_ = lean_unsigned_to_nat(0u);
v___x_4428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4426_, v___x_4427_, v_x_4412_);
return v___x_4428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4429_, lean_object* v_x_4430_, lean_object* v_x_4431_){
_start:
{
size_t v_x_2353__boxed_4432_; uint8_t v_res_4433_; lean_object* v_r_4434_; 
v_x_2353__boxed_4432_ = lean_unbox_usize(v_x_4430_);
lean_dec(v_x_4430_);
v_res_4433_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4429_, v_x_2353__boxed_4432_, v_x_4431_);
lean_dec(v_x_4431_);
lean_dec_ref(v_x_4429_);
v_r_4434_ = lean_box(v_res_4433_);
return v_r_4434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4435_, lean_object* v_x_4436_){
_start:
{
uint64_t v___y_4438_; 
if (lean_obj_tag(v_x_4436_) == 0)
{
uint64_t v___x_4441_; 
v___x_4441_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4438_ = v___x_4441_;
goto v___jp_4437_;
}
else
{
uint64_t v_hash_4442_; 
v_hash_4442_ = lean_ctor_get_uint64(v_x_4436_, sizeof(void*)*2);
v___y_4438_ = v_hash_4442_;
goto v___jp_4437_;
}
v___jp_4437_:
{
size_t v___x_4439_; uint8_t v___x_4440_; 
v___x_4439_ = lean_uint64_to_usize(v___y_4438_);
v___x_4440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4435_, v___x_4439_, v_x_4436_);
return v___x_4440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4443_, lean_object* v_x_4444_){
_start:
{
uint8_t v_res_4445_; lean_object* v_r_4446_; 
v_res_4445_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4443_, v_x_4444_);
lean_dec(v_x_4444_);
lean_dec_ref(v_x_4443_);
v_r_4446_ = lean_box(v_res_4445_);
return v_r_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4447_, lean_object* v_declName_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_instanceNames_4455_; uint8_t v___x_4456_; 
v_instanceNames_4455_ = lean_ctor_get(v_d_4447_, 1);
v___x_4456_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4455_, v_declName_4448_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v_d_4447_);
v___x_4457_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4458_ = l_Lean_MessageData_ofConstName(v_declName_4448_, v___x_4456_);
v___x_4459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4457_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
v___x_4460_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4459_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4461_, v___y_4449_, v___y_4450_);
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4462_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4462_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
else
{
goto v___jp_4452_;
}
v___jp_4452_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = l_Lean_Meta_Instances_eraseCore(v_d_4447_, v_declName_4448_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4471_, lean_object* v_declName_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4471_, v_declName_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4477_, lean_object* v_declName_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; lean_object* v_env_4483_; lean_object* v___x_4484_; lean_object* v_ext_4485_; lean_object* v_toEnvExtension_4486_; lean_object* v_asyncMode_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4482_ = lean_st_ref_get(v___y_4480_);
v_env_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc_ref(v_env_4483_);
lean_dec(v___x_4482_);
v___x_4484_ = l_Lean_Meta_instanceExtension;
v_ext_4485_ = lean_ctor_get(v___x_4484_, 1);
v_toEnvExtension_4486_ = lean_ctor_get(v_ext_4485_, 0);
v_asyncMode_4487_ = lean_ctor_get(v_toEnvExtension_4486_, 2);
v___x_4488_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4477_, v___x_4484_, v_env_4483_, v_asyncMode_4487_);
v___x_4489_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4488_, v_declName_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4519_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4519_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4519_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v_env_4495_; lean_object* v_nextMacroScope_4496_; lean_object* v_ngen_4497_; lean_object* v_auxDeclNGen_4498_; lean_object* v_traceState_4499_; lean_object* v_messages_4500_; lean_object* v_infoState_4501_; lean_object* v_snapshotTasks_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4517_; 
v___x_4494_ = lean_st_ref_take(v___y_4480_);
v_env_4495_ = lean_ctor_get(v___x_4494_, 0);
v_nextMacroScope_4496_ = lean_ctor_get(v___x_4494_, 1);
v_ngen_4497_ = lean_ctor_get(v___x_4494_, 2);
v_auxDeclNGen_4498_ = lean_ctor_get(v___x_4494_, 3);
v_traceState_4499_ = lean_ctor_get(v___x_4494_, 4);
v_messages_4500_ = lean_ctor_get(v___x_4494_, 6);
v_infoState_4501_ = lean_ctor_get(v___x_4494_, 7);
v_snapshotTasks_4502_ = lean_ctor_get(v___x_4494_, 8);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v___x_4494_, 5);
lean_dec(v_unused_4518_);
v___x_4504_ = v___x_4494_;
v_isShared_4505_ = v_isSharedCheck_4517_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_snapshotTasks_4502_);
lean_inc(v_infoState_4501_);
lean_inc(v_messages_4500_);
lean_inc(v_traceState_4499_);
lean_inc(v_auxDeclNGen_4498_);
lean_inc(v_ngen_4497_);
lean_inc(v_nextMacroScope_4496_);
lean_inc(v_env_4495_);
lean_dec(v___x_4494_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4517_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___f_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___f_4506_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4506_, 0, v_a_4490_);
v___x_4507_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4484_, v_env_4495_, v___f_4506_);
v___x_4508_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 5, v___x_4508_);
lean_ctor_set(v___x_4504_, 0, v___x_4507_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v_nextMacroScope_4496_);
lean_ctor_set(v_reuseFailAlloc_4516_, 2, v_ngen_4497_);
lean_ctor_set(v_reuseFailAlloc_4516_, 3, v_auxDeclNGen_4498_);
lean_ctor_set(v_reuseFailAlloc_4516_, 4, v_traceState_4499_);
lean_ctor_set(v_reuseFailAlloc_4516_, 5, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4516_, 6, v_messages_4500_);
lean_ctor_set(v_reuseFailAlloc_4516_, 7, v_infoState_4501_);
lean_ctor_set(v_reuseFailAlloc_4516_, 8, v_snapshotTasks_4502_);
v___x_4510_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4511_ = lean_st_ref_set(v___y_4480_, v___x_4510_);
v___x_4512_ = lean_box(0);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4512_);
v___x_4514_ = v___x_4492_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
v_a_4520_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4489_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4489_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4528_, lean_object* v_declName_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4528_, v_declName_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec_ref(v___x_4528_);
return v_res_4533_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4540_; uint64_t v___x_4541_; 
v___x_4540_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4540_);
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4543_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
lean_ctor_set_uint64(v___x_4544_, sizeof(void*)*1, v___x_4542_);
return v___x_4544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4549_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
lean_ctor_set(v___x_4549_, 2, v___x_4548_);
lean_ctor_set(v___x_4549_, 3, v___x_4548_);
lean_ctor_set(v___x_4549_, 4, v___x_4548_);
lean_ctor_set(v___x_4549_, 5, v___x_4548_);
return v___x_4549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
lean_ctor_set(v___x_4551_, 2, v___x_4550_);
lean_ctor_set(v___x_4551_, 3, v___x_4550_);
lean_ctor_set(v___x_4551_, 4, v___x_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4552_, lean_object* v___x_4553_, lean_object* v_declName_4554_, lean_object* v_stx_4555_, uint8_t v_attrKind_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4560_ = lean_unsigned_to_nat(1u);
v___x_4561_ = l_Lean_Syntax_getArg(v_stx_4555_, v___x_4560_);
v___x_4562_ = l_Lean_getAttrParamOptPrio(v___x_4561_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; uint8_t v___x_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; size_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref(v___x_4562_);
v___x_4564_ = 0;
v___x_4565_ = 1;
v___x_4566_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4567_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4568_ = lean_unsigned_to_nat(32u);
v___x_4569_ = lean_mk_empty_array_with_capacity(v___x_4568_);
v___x_4570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4571_ = ((size_t)5ULL);
lean_inc_n(v___x_4552_, 6);
v___x_4572_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set(v___x_4572_, 1, v___x_4569_);
lean_ctor_set(v___x_4572_, 2, v___x_4552_);
lean_ctor_set(v___x_4572_, 3, v___x_4552_);
lean_ctor_set_usize(v___x_4572_, 4, v___x_4571_);
v___x_4573_ = lean_box(1);
lean_inc_ref(v___x_4572_);
v___x_4574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4567_);
lean_ctor_set(v___x_4574_, 1, v___x_4572_);
lean_ctor_set(v___x_4574_, 2, v___x_4573_);
v___x_4575_ = lean_mk_empty_array_with_capacity(v___x_4552_);
v___x_4576_ = lean_box(0);
lean_inc(v___x_4553_);
v___x_4577_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4577_, 0, v___x_4566_);
lean_ctor_set(v___x_4577_, 1, v___x_4553_);
lean_ctor_set(v___x_4577_, 2, v___x_4574_);
lean_ctor_set(v___x_4577_, 3, v___x_4575_);
lean_ctor_set(v___x_4577_, 4, v___x_4576_);
lean_ctor_set(v___x_4577_, 5, v___x_4552_);
lean_ctor_set(v___x_4577_, 6, v___x_4576_);
lean_ctor_set_uint8(v___x_4577_, sizeof(void*)*7, v___x_4564_);
lean_ctor_set_uint8(v___x_4577_, sizeof(void*)*7 + 1, v___x_4564_);
lean_ctor_set_uint8(v___x_4577_, sizeof(void*)*7 + 2, v___x_4564_);
lean_ctor_set_uint8(v___x_4577_, sizeof(void*)*7 + 3, v___x_4565_);
v___x_4578_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4552_);
lean_ctor_set(v___x_4578_, 1, v___x_4552_);
lean_ctor_set(v___x_4578_, 2, v___x_4552_);
lean_ctor_set(v___x_4578_, 3, v___x_4552_);
lean_ctor_set(v___x_4578_, 4, v___x_4567_);
lean_ctor_set(v___x_4578_, 5, v___x_4567_);
lean_ctor_set(v___x_4578_, 6, v___x_4567_);
lean_ctor_set(v___x_4578_, 7, v___x_4567_);
lean_ctor_set(v___x_4578_, 8, v___x_4567_);
lean_ctor_set(v___x_4578_, 9, v___x_4567_);
v___x_4579_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4580_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4578_);
lean_ctor_set(v___x_4581_, 1, v___x_4579_);
lean_ctor_set(v___x_4581_, 2, v___x_4553_);
lean_ctor_set(v___x_4581_, 3, v___x_4572_);
lean_ctor_set(v___x_4581_, 4, v___x_4580_);
v___x_4582_ = lean_st_mk_ref(v___x_4581_);
v___x_4583_ = l_Lean_Meta_addInstance(v_declName_4554_, v_attrKind_4556_, v_a_4563_, v___x_4577_, v___x_4582_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___x_4577_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4592_; 
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; 
v_unused_4593_ = lean_ctor_get(v___x_4583_, 0);
lean_dec(v_unused_4593_);
v___x_4585_ = v___x_4583_;
v_isShared_4586_ = v_isSharedCheck_4592_;
goto v_resetjp_4584_;
}
else
{
lean_dec(v___x_4583_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4592_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4587_ = lean_st_ref_get(v___x_4582_);
lean_dec(v___x_4582_);
lean_dec(v___x_4587_);
v___x_4588_ = lean_box(0);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v___x_4588_);
v___x_4590_ = v___x_4585_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
else
{
lean_dec(v___x_4582_);
return v___x_4583_;
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_dec(v_declName_4554_);
lean_dec(v___x_4553_);
lean_dec(v___x_4552_);
v_a_4594_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4562_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4562_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4602_, lean_object* v___x_4603_, lean_object* v_declName_4604_, lean_object* v_stx_4605_, lean_object* v_attrKind_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v_attrKind_boxed_4610_; lean_object* v_res_4611_; 
v_attrKind_boxed_4610_ = lean_unbox(v_attrKind_4606_);
v_res_4611_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4602_, v___x_4603_, v_declName_4604_, v_stx_4605_, v_attrKind_boxed_4610_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v_stx_4605_);
return v_res_4611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4612_; lean_object* v___f_4613_; 
v___x_4612_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4613_, 0, v___x_4612_);
return v___f_4613_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4680_; lean_object* v___f_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___f_4680_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4681_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4682_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v___f_4681_);
lean_ctor_set(v___x_4683_, 2, v___f_4680_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4686_ = l_Lean_registerBuiltinAttribute(v___x_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4688_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4689_, lean_object* v_x_4690_, lean_object* v_x_4691_){
_start:
{
uint8_t v___x_4692_; 
v___x_4692_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4690_, v_x_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4693_, lean_object* v_x_4694_, lean_object* v_x_4695_){
_start:
{
uint8_t v_res_4696_; lean_object* v_r_4697_; 
v_res_4696_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4693_, v_x_4694_, v_x_4695_);
lean_dec(v_x_4695_);
lean_dec_ref(v_x_4694_);
v_r_4697_ = lean_box(v_res_4696_);
return v_r_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4698_, lean_object* v_msg_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4699_, v___y_4700_, v___y_4701_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4704_, lean_object* v_msg_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4704_, v_msg_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
return v_res_4709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4710_, lean_object* v_x_4711_, size_t v_x_4712_, lean_object* v_x_4713_){
_start:
{
uint8_t v___x_4714_; 
v___x_4714_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4711_, v_x_4712_, v_x_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4715_, lean_object* v_x_4716_, lean_object* v_x_4717_, lean_object* v_x_4718_){
_start:
{
size_t v_x_3005__boxed_4719_; uint8_t v_res_4720_; lean_object* v_r_4721_; 
v_x_3005__boxed_4719_ = lean_unbox_usize(v_x_4717_);
lean_dec(v_x_4717_);
v_res_4720_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4715_, v_x_4716_, v_x_3005__boxed_4719_, v_x_4718_);
lean_dec(v_x_4718_);
lean_dec_ref(v_x_4716_);
v_r_4721_ = lean_box(v_res_4720_);
return v_r_4721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4722_, lean_object* v_keys_4723_, lean_object* v_vals_4724_, lean_object* v_heq_4725_, lean_object* v_i_4726_, lean_object* v_k_4727_){
_start:
{
uint8_t v___x_4728_; 
v___x_4728_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4723_, v_i_4726_, v_k_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4729_, lean_object* v_keys_4730_, lean_object* v_vals_4731_, lean_object* v_heq_4732_, lean_object* v_i_4733_, lean_object* v_k_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4729_, v_keys_4730_, v_vals_4731_, v_heq_4732_, v_i_4733_, v_k_4734_);
lean_dec(v_k_4734_);
lean_dec_ref(v_vals_4731_);
lean_dec_ref(v_keys_4730_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4739_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4740_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4741_ = l_Lean_addBuiltinDocString(v___x_4739_, v___x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4746_; lean_object* v_env_4747_; lean_object* v___x_4748_; lean_object* v_ext_4749_; lean_object* v_toEnvExtension_4750_; lean_object* v_asyncMode_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v_discrTree_4754_; lean_object* v___x_4755_; 
v___x_4746_ = lean_st_ref_get(v_a_4744_);
v_env_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc_ref(v_env_4747_);
lean_dec(v___x_4746_);
v___x_4748_ = l_Lean_Meta_instanceExtension;
v_ext_4749_ = lean_ctor_get(v___x_4748_, 1);
v_toEnvExtension_4750_ = lean_ctor_get(v_ext_4749_, 0);
v_asyncMode_4751_ = lean_ctor_get(v_toEnvExtension_4750_, 2);
v___x_4752_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4753_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4752_, v___x_4748_, v_env_4747_, v_asyncMode_4751_);
v_discrTree_4754_ = lean_ctor_get(v___x_4753_, 0);
lean_inc_ref(v_discrTree_4754_);
lean_dec(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4755_, 0, v_discrTree_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4756_);
lean_dec(v_a_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4763_, v_a_4764_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; lean_object* v_env_4770_; lean_object* v___x_4771_; lean_object* v_ext_4772_; lean_object* v_toEnvExtension_4773_; lean_object* v_asyncMode_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v_erased_4777_; lean_object* v___x_4778_; 
v___x_4769_ = lean_st_ref_get(v_a_4767_);
v_env_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc_ref(v_env_4770_);
lean_dec(v___x_4769_);
v___x_4771_ = l_Lean_Meta_instanceExtension;
v_ext_4772_ = lean_ctor_get(v___x_4771_, 1);
v_toEnvExtension_4773_ = lean_ctor_get(v_ext_4772_, 0);
v_asyncMode_4774_ = lean_ctor_get(v_toEnvExtension_4773_, 2);
v___x_4775_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4776_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4775_, v___x_4771_, v_env_4770_, v_asyncMode_4774_);
v_erased_4777_ = lean_ctor_get(v___x_4776_, 2);
lean_inc_ref(v_erased_4777_);
lean_dec(v___x_4776_);
v___x_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4778_, 0, v_erased_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4779_);
lean_dec(v_a_4779_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4783_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Lean_Meta_getErasedInstances(v_a_4786_, v_a_4787_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
return v_res_4789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4790_, lean_object* v_declName_4791_){
_start:
{
lean_object* v___x_4792_; lean_object* v_ext_4793_; lean_object* v_toEnvExtension_4794_; lean_object* v_asyncMode_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v_instanceNames_4798_; uint8_t v___x_4799_; 
v___x_4792_ = l_Lean_Meta_instanceExtension;
v_ext_4793_ = lean_ctor_get(v___x_4792_, 1);
v_toEnvExtension_4794_ = lean_ctor_get(v_ext_4793_, 0);
v_asyncMode_4795_ = lean_ctor_get(v_toEnvExtension_4794_, 2);
v___x_4796_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4797_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4796_, v___x_4792_, v_env_4790_, v_asyncMode_4795_);
v_instanceNames_4798_ = lean_ctor_get(v___x_4797_, 1);
lean_inc_ref(v_instanceNames_4798_);
lean_dec(v___x_4797_);
v___x_4799_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4798_, v_declName_4791_);
lean_dec_ref(v_instanceNames_4798_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4800_, lean_object* v_declName_4801_){
_start:
{
uint8_t v_res_4802_; lean_object* v_r_4803_; 
v_res_4802_ = l_Lean_Meta_isInstanceCore(v_env_4800_, v_declName_4801_);
lean_dec(v_declName_4801_);
v_r_4803_ = lean_box(v_res_4802_);
return v_r_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v___x_4807_; lean_object* v_env_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4807_ = lean_st_ref_get(v_a_4805_);
v_env_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc_ref(v_env_4808_);
lean_dec(v___x_4807_);
v___x_4809_ = l_Lean_Meta_isInstanceCore(v_env_4808_, v_declName_4804_);
v___x_4810_ = lean_box(v___x_4809_);
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l_Lean_Meta_isInstance___redArg(v_declName_4812_, v_a_4813_);
lean_dec(v_a_4813_);
lean_dec(v_declName_4812_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_Meta_isInstance___redArg(v_declName_4816_, v_a_4818_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Meta_isInstance(v_declName_4821_, v_a_4822_, v_a_4823_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_declName_4821_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4826_, lean_object* v_vals_4827_, lean_object* v_i_4828_, lean_object* v_k_4829_){
_start:
{
lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4830_ = lean_array_get_size(v_keys_4826_);
v___x_4831_ = lean_nat_dec_lt(v_i_4828_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; 
lean_dec(v_i_4828_);
v___x_4832_ = lean_box(0);
return v___x_4832_;
}
else
{
lean_object* v_k_x27_4833_; uint8_t v___x_4834_; 
v_k_x27_4833_ = lean_array_fget_borrowed(v_keys_4826_, v_i_4828_);
v___x_4834_ = lean_name_eq(v_k_4829_, v_k_x27_4833_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = lean_nat_add(v_i_4828_, v___x_4835_);
lean_dec(v_i_4828_);
v_i_4828_ = v___x_4836_;
goto _start;
}
else
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_array_fget_borrowed(v_vals_4827_, v_i_4828_);
lean_dec(v_i_4828_);
lean_inc(v___x_4838_);
v___x_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4838_);
return v___x_4839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4840_, lean_object* v_vals_4841_, lean_object* v_i_4842_, lean_object* v_k_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4840_, v_vals_4841_, v_i_4842_, v_k_4843_);
lean_dec(v_k_4843_);
lean_dec_ref(v_vals_4841_);
lean_dec_ref(v_keys_4840_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4845_, size_t v_x_4846_, lean_object* v_x_4847_){
_start:
{
if (lean_obj_tag(v_x_4845_) == 0)
{
lean_object* v_es_4848_; lean_object* v___x_4849_; size_t v___x_4850_; size_t v___x_4851_; size_t v___x_4852_; lean_object* v_j_4853_; lean_object* v___x_4854_; 
v_es_4848_ = lean_ctor_get(v_x_4845_, 0);
v___x_4849_ = lean_box(2);
v___x_4850_ = ((size_t)5ULL);
v___x_4851_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4852_ = lean_usize_land(v_x_4846_, v___x_4851_);
v_j_4853_ = lean_usize_to_nat(v___x_4852_);
v___x_4854_ = lean_array_get_borrowed(v___x_4849_, v_es_4848_, v_j_4853_);
lean_dec(v_j_4853_);
switch(lean_obj_tag(v___x_4854_))
{
case 0:
{
lean_object* v_key_4855_; lean_object* v_val_4856_; uint8_t v___x_4857_; 
v_key_4855_ = lean_ctor_get(v___x_4854_, 0);
v_val_4856_ = lean_ctor_get(v___x_4854_, 1);
v___x_4857_ = lean_name_eq(v_x_4847_, v_key_4855_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_box(0);
return v___x_4858_;
}
else
{
lean_object* v___x_4859_; 
lean_inc(v_val_4856_);
v___x_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4859_, 0, v_val_4856_);
return v___x_4859_;
}
}
case 1:
{
lean_object* v_node_4860_; size_t v___x_4861_; 
v_node_4860_ = lean_ctor_get(v___x_4854_, 0);
v___x_4861_ = lean_usize_shift_right(v_x_4846_, v___x_4850_);
v_x_4845_ = v_node_4860_;
v_x_4846_ = v___x_4861_;
goto _start;
}
default: 
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_box(0);
return v___x_4863_;
}
}
}
else
{
lean_object* v_ks_4864_; lean_object* v_vs_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v_ks_4864_ = lean_ctor_get(v_x_4845_, 0);
v_vs_4865_ = lean_ctor_get(v_x_4845_, 1);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4864_, v_vs_4865_, v___x_4866_, v_x_4847_);
return v___x_4867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4868_, lean_object* v_x_4869_, lean_object* v_x_4870_){
_start:
{
size_t v_x_489__boxed_4871_; lean_object* v_res_4872_; 
v_x_489__boxed_4871_ = lean_unbox_usize(v_x_4869_);
lean_dec(v_x_4869_);
v_res_4872_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4868_, v_x_489__boxed_4871_, v_x_4870_);
lean_dec(v_x_4870_);
lean_dec_ref(v_x_4868_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4873_, lean_object* v_x_4874_){
_start:
{
uint64_t v___y_4876_; 
if (lean_obj_tag(v_x_4874_) == 0)
{
uint64_t v___x_4879_; 
v___x_4879_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4876_ = v___x_4879_;
goto v___jp_4875_;
}
else
{
uint64_t v_hash_4880_; 
v_hash_4880_ = lean_ctor_get_uint64(v_x_4874_, sizeof(void*)*2);
v___y_4876_ = v_hash_4880_;
goto v___jp_4875_;
}
v___jp_4875_:
{
size_t v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_uint64_to_usize(v___y_4876_);
v___x_4878_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4873_, v___x_4877_, v_x_4874_);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4881_, lean_object* v_x_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4881_, v_x_4882_);
lean_dec(v_x_4882_);
lean_dec_ref(v_x_4881_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v___x_4887_; lean_object* v_env_4888_; lean_object* v___x_4889_; lean_object* v_ext_4890_; lean_object* v_toEnvExtension_4891_; lean_object* v_asyncMode_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v_instanceNames_4895_; lean_object* v___x_4896_; 
v___x_4887_ = lean_st_ref_get(v_a_4885_);
v_env_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc_ref(v_env_4888_);
lean_dec(v___x_4887_);
v___x_4889_ = l_Lean_Meta_instanceExtension;
v_ext_4890_ = lean_ctor_get(v___x_4889_, 1);
v_toEnvExtension_4891_ = lean_ctor_get(v_ext_4890_, 0);
v_asyncMode_4892_ = lean_ctor_get(v_toEnvExtension_4891_, 2);
v___x_4893_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4894_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4893_, v___x_4889_, v_env_4888_, v_asyncMode_4892_);
v_instanceNames_4895_ = lean_ctor_get(v___x_4894_, 1);
lean_inc_ref(v_instanceNames_4895_);
lean_dec(v___x_4894_);
v___x_4896_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4895_, v_declName_4884_);
lean_dec_ref(v_instanceNames_4895_);
if (lean_obj_tag(v___x_4896_) == 1)
{
lean_object* v_val_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4906_; 
v_val_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_val_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v_priority_4901_; lean_object* v___x_4903_; 
v_priority_4901_ = lean_ctor_get(v_val_4897_, 2);
lean_inc(v_priority_4901_);
lean_dec(v_val_4897_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v_priority_4901_);
v___x_4903_ = v___x_4899_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_priority_4901_);
v___x_4903_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; 
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
}
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_dec(v___x_4896_);
v___x_4907_ = lean_box(0);
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
return v___x_4908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4909_, v_a_4910_);
lean_dec(v_a_4910_);
lean_dec(v_declName_4909_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4913_, v_a_4915_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_declName_4918_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4923_, lean_object* v_x_4924_, lean_object* v_x_4925_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4924_, v_x_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4927_, lean_object* v_x_4928_, lean_object* v_x_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4927_, v_x_4928_, v_x_4929_);
lean_dec(v_x_4929_);
lean_dec_ref(v_x_4928_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4931_, lean_object* v_x_4932_, size_t v_x_4933_, lean_object* v_x_4934_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4932_, v_x_4933_, v_x_4934_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4936_, lean_object* v_x_4937_, lean_object* v_x_4938_, lean_object* v_x_4939_){
_start:
{
size_t v_x_605__boxed_4940_; lean_object* v_res_4941_; 
v_x_605__boxed_4940_ = lean_unbox_usize(v_x_4938_);
lean_dec(v_x_4938_);
v_res_4941_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4936_, v_x_4937_, v_x_605__boxed_4940_, v_x_4939_);
lean_dec(v_x_4939_);
lean_dec_ref(v_x_4937_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4942_, lean_object* v_keys_4943_, lean_object* v_vals_4944_, lean_object* v_heq_4945_, lean_object* v_i_4946_, lean_object* v_k_4947_){
_start:
{
lean_object* v___x_4948_; 
v___x_4948_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4943_, v_vals_4944_, v_i_4946_, v_k_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4949_, lean_object* v_keys_4950_, lean_object* v_vals_4951_, lean_object* v_heq_4952_, lean_object* v_i_4953_, lean_object* v_k_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4949_, v_keys_4950_, v_vals_4951_, v_heq_4952_, v_i_4953_, v_k_4954_);
lean_dec(v_k_4954_);
lean_dec_ref(v_vals_4951_);
lean_dec_ref(v_keys_4950_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v___x_4959_; lean_object* v_env_4960_; lean_object* v___x_4961_; lean_object* v_ext_4962_; lean_object* v_toEnvExtension_4963_; lean_object* v_asyncMode_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v_instanceNames_4967_; lean_object* v___x_4968_; 
v___x_4959_ = lean_st_ref_get(v_a_4957_);
v_env_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc_ref(v_env_4960_);
lean_dec(v___x_4959_);
v___x_4961_ = l_Lean_Meta_instanceExtension;
v_ext_4962_ = lean_ctor_get(v___x_4961_, 1);
v_toEnvExtension_4963_ = lean_ctor_get(v_ext_4962_, 0);
v_asyncMode_4964_ = lean_ctor_get(v_toEnvExtension_4963_, 2);
v___x_4965_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4966_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4965_, v___x_4961_, v_env_4960_, v_asyncMode_4964_);
v_instanceNames_4967_ = lean_ctor_get(v___x_4966_, 1);
lean_inc_ref(v_instanceNames_4967_);
lean_dec(v___x_4966_);
v___x_4968_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4967_, v_declName_4956_);
lean_dec_ref(v_instanceNames_4967_);
if (lean_obj_tag(v___x_4968_) == 1)
{
lean_object* v_val_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4979_; 
v_val_4969_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4971_ = v___x_4968_;
v_isShared_4972_ = v_isSharedCheck_4979_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_val_4969_);
lean_dec(v___x_4968_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4979_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
uint8_t v_attrKind_4973_; lean_object* v___x_4974_; lean_object* v___x_4976_; 
v_attrKind_4973_ = lean_ctor_get_uint8(v_val_4969_, sizeof(void*)*5);
lean_dec(v_val_4969_);
v___x_4974_ = lean_box(v_attrKind_4973_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 0, v___x_4974_);
v___x_4976_ = v___x_4971_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4974_);
v___x_4976_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
return v___x_4977_;
}
}
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
lean_dec(v___x_4968_);
v___x_4980_ = lean_box(0);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4982_, v_a_4983_);
lean_dec(v_a_4983_);
lean_dec(v_declName_4982_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_){
_start:
{
lean_object* v___x_4990_; 
v___x_4990_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4986_, v_a_4988_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_declName_4991_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5000_, lean_object* v_v_5001_, lean_object* v_t_5002_){
_start:
{
if (lean_obj_tag(v_t_5002_) == 0)
{
lean_object* v_size_5003_; lean_object* v_k_5004_; lean_object* v_v_5005_; lean_object* v_l_5006_; lean_object* v_r_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5288_; 
v_size_5003_ = lean_ctor_get(v_t_5002_, 0);
v_k_5004_ = lean_ctor_get(v_t_5002_, 1);
v_v_5005_ = lean_ctor_get(v_t_5002_, 2);
v_l_5006_ = lean_ctor_get(v_t_5002_, 3);
v_r_5007_ = lean_ctor_get(v_t_5002_, 4);
v_isSharedCheck_5288_ = !lean_is_exclusive(v_t_5002_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5009_ = v_t_5002_;
v_isShared_5010_ = v_isSharedCheck_5288_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_r_5007_);
lean_inc(v_l_5006_);
lean_inc(v_v_5005_);
lean_inc(v_k_5004_);
lean_inc(v_size_5003_);
lean_dec(v_t_5002_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5288_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
uint8_t v___x_5011_; 
v___x_5011_ = lean_nat_dec_lt(v_k_5004_, v_k_5000_);
if (v___x_5011_ == 0)
{
uint8_t v___x_5012_; 
v___x_5012_ = lean_nat_dec_eq(v_k_5004_, v_k_5000_);
if (v___x_5012_ == 0)
{
lean_object* v_impl_5013_; lean_object* v___x_5014_; 
lean_dec(v_size_5003_);
v_impl_5013_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5000_, v_v_5001_, v_r_5007_);
v___x_5014_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5006_) == 0)
{
lean_object* v_size_5015_; lean_object* v_size_5016_; lean_object* v_k_5017_; lean_object* v_v_5018_; lean_object* v_l_5019_; lean_object* v_r_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_size_5015_ = lean_ctor_get(v_l_5006_, 0);
v_size_5016_ = lean_ctor_get(v_impl_5013_, 0);
lean_inc(v_size_5016_);
v_k_5017_ = lean_ctor_get(v_impl_5013_, 1);
lean_inc(v_k_5017_);
v_v_5018_ = lean_ctor_get(v_impl_5013_, 2);
lean_inc(v_v_5018_);
v_l_5019_ = lean_ctor_get(v_impl_5013_, 3);
lean_inc(v_l_5019_);
v_r_5020_ = lean_ctor_get(v_impl_5013_, 4);
lean_inc(v_r_5020_);
v___x_5021_ = lean_unsigned_to_nat(3u);
v___x_5022_ = lean_nat_mul(v___x_5021_, v_size_5015_);
v___x_5023_ = lean_nat_dec_lt(v___x_5022_, v_size_5016_);
lean_dec(v___x_5022_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5027_; 
lean_dec(v_r_5020_);
lean_dec(v_l_5019_);
lean_dec(v_v_5018_);
lean_dec(v_k_5017_);
v___x_5024_ = lean_nat_add(v___x_5014_, v_size_5015_);
v___x_5025_ = lean_nat_add(v___x_5024_, v_size_5016_);
lean_dec(v_size_5016_);
lean_dec(v___x_5024_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_impl_5013_);
lean_ctor_set(v___x_5009_, 0, v___x_5025_);
v___x_5027_ = v___x_5009_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5025_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5028_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5028_, 3, v_l_5006_);
lean_ctor_set(v_reuseFailAlloc_5028_, 4, v_impl_5013_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
else
{
lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5092_; 
v_isSharedCheck_5092_ = !lean_is_exclusive(v_impl_5013_);
if (v_isSharedCheck_5092_ == 0)
{
lean_object* v_unused_5093_; lean_object* v_unused_5094_; lean_object* v_unused_5095_; lean_object* v_unused_5096_; lean_object* v_unused_5097_; 
v_unused_5093_ = lean_ctor_get(v_impl_5013_, 4);
lean_dec(v_unused_5093_);
v_unused_5094_ = lean_ctor_get(v_impl_5013_, 3);
lean_dec(v_unused_5094_);
v_unused_5095_ = lean_ctor_get(v_impl_5013_, 2);
lean_dec(v_unused_5095_);
v_unused_5096_ = lean_ctor_get(v_impl_5013_, 1);
lean_dec(v_unused_5096_);
v_unused_5097_ = lean_ctor_get(v_impl_5013_, 0);
lean_dec(v_unused_5097_);
v___x_5030_ = v_impl_5013_;
v_isShared_5031_ = v_isSharedCheck_5092_;
goto v_resetjp_5029_;
}
else
{
lean_dec(v_impl_5013_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5092_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v_size_5032_; lean_object* v_k_5033_; lean_object* v_v_5034_; lean_object* v_l_5035_; lean_object* v_r_5036_; lean_object* v_size_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v_size_5032_ = lean_ctor_get(v_l_5019_, 0);
v_k_5033_ = lean_ctor_get(v_l_5019_, 1);
v_v_5034_ = lean_ctor_get(v_l_5019_, 2);
v_l_5035_ = lean_ctor_get(v_l_5019_, 3);
v_r_5036_ = lean_ctor_get(v_l_5019_, 4);
v_size_5037_ = lean_ctor_get(v_r_5020_, 0);
v___x_5038_ = lean_unsigned_to_nat(2u);
v___x_5039_ = lean_nat_mul(v___x_5038_, v_size_5037_);
v___x_5040_ = lean_nat_dec_lt(v_size_5032_, v___x_5039_);
lean_dec(v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5068_; 
lean_inc(v_r_5036_);
lean_inc(v_l_5035_);
lean_inc(v_v_5034_);
lean_inc(v_k_5033_);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_l_5019_);
if (v_isSharedCheck_5068_ == 0)
{
lean_object* v_unused_5069_; lean_object* v_unused_5070_; lean_object* v_unused_5071_; lean_object* v_unused_5072_; lean_object* v_unused_5073_; 
v_unused_5069_ = lean_ctor_get(v_l_5019_, 4);
lean_dec(v_unused_5069_);
v_unused_5070_ = lean_ctor_get(v_l_5019_, 3);
lean_dec(v_unused_5070_);
v_unused_5071_ = lean_ctor_get(v_l_5019_, 2);
lean_dec(v_unused_5071_);
v_unused_5072_ = lean_ctor_get(v_l_5019_, 1);
lean_dec(v_unused_5072_);
v_unused_5073_ = lean_ctor_get(v_l_5019_, 0);
lean_dec(v_unused_5073_);
v___x_5042_ = v_l_5019_;
v_isShared_5043_ = v_isSharedCheck_5068_;
goto v_resetjp_5041_;
}
else
{
lean_dec(v_l_5019_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5068_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5058_; 
v___x_5044_ = lean_nat_add(v___x_5014_, v_size_5015_);
v___x_5045_ = lean_nat_add(v___x_5044_, v_size_5016_);
lean_dec(v_size_5016_);
if (lean_obj_tag(v_l_5035_) == 0)
{
lean_object* v_size_5066_; 
v_size_5066_ = lean_ctor_get(v_l_5035_, 0);
lean_inc(v_size_5066_);
v___y_5058_ = v_size_5066_;
goto v___jp_5057_;
}
else
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_unsigned_to_nat(0u);
v___y_5058_ = v___x_5067_;
goto v___jp_5057_;
}
v___jp_5046_:
{
lean_object* v___x_5050_; lean_object* v___x_5052_; 
v___x_5050_ = lean_nat_add(v___y_5047_, v___y_5049_);
lean_dec(v___y_5049_);
lean_dec(v___y_5047_);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 4, v_r_5020_);
lean_ctor_set(v___x_5042_, 3, v_r_5036_);
lean_ctor_set(v___x_5042_, 2, v_v_5018_);
lean_ctor_set(v___x_5042_, 1, v_k_5017_);
lean_ctor_set(v___x_5042_, 0, v___x_5050_);
v___x_5052_ = v___x_5042_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5050_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v_k_5017_);
lean_ctor_set(v_reuseFailAlloc_5056_, 2, v_v_5018_);
lean_ctor_set(v_reuseFailAlloc_5056_, 3, v_r_5036_);
lean_ctor_set(v_reuseFailAlloc_5056_, 4, v_r_5020_);
v___x_5052_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5054_; 
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 4, v___x_5052_);
lean_ctor_set(v___x_5030_, 3, v___y_5048_);
lean_ctor_set(v___x_5030_, 2, v_v_5034_);
lean_ctor_set(v___x_5030_, 1, v_k_5033_);
lean_ctor_set(v___x_5030_, 0, v___x_5045_);
v___x_5054_ = v___x_5030_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_k_5033_);
lean_ctor_set(v_reuseFailAlloc_5055_, 2, v_v_5034_);
lean_ctor_set(v_reuseFailAlloc_5055_, 3, v___y_5048_);
lean_ctor_set(v_reuseFailAlloc_5055_, 4, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
v___jp_5057_:
{
lean_object* v___x_5059_; lean_object* v___x_5061_; 
v___x_5059_ = lean_nat_add(v___x_5044_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec(v___x_5044_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_l_5035_);
lean_ctor_set(v___x_5009_, 0, v___x_5059_);
v___x_5061_ = v___x_5009_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_l_5006_);
lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_l_5035_);
v___x_5061_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
lean_object* v___x_5062_; 
v___x_5062_ = lean_nat_add(v___x_5014_, v_size_5037_);
if (lean_obj_tag(v_r_5036_) == 0)
{
lean_object* v_size_5063_; 
v_size_5063_ = lean_ctor_get(v_r_5036_, 0);
lean_inc(v_size_5063_);
v___y_5047_ = v___x_5062_;
v___y_5048_ = v___x_5061_;
v___y_5049_ = v_size_5063_;
goto v___jp_5046_;
}
else
{
lean_object* v___x_5064_; 
v___x_5064_ = lean_unsigned_to_nat(0u);
v___y_5047_ = v___x_5062_;
v___y_5048_ = v___x_5061_;
v___y_5049_ = v___x_5064_;
goto v___jp_5046_;
}
}
}
}
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5078_; 
lean_del_object(v___x_5009_);
v___x_5074_ = lean_nat_add(v___x_5014_, v_size_5015_);
v___x_5075_ = lean_nat_add(v___x_5074_, v_size_5016_);
lean_dec(v_size_5016_);
v___x_5076_ = lean_nat_add(v___x_5074_, v_size_5032_);
lean_dec(v___x_5074_);
lean_inc_ref(v_l_5006_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 4, v_l_5019_);
lean_ctor_set(v___x_5030_, 3, v_l_5006_);
lean_ctor_set(v___x_5030_, 2, v_v_5005_);
lean_ctor_set(v___x_5030_, 1, v_k_5004_);
lean_ctor_set(v___x_5030_, 0, v___x_5076_);
v___x_5078_ = v___x_5030_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5091_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5091_, 3, v_l_5006_);
lean_ctor_set(v_reuseFailAlloc_5091_, 4, v_l_5019_);
v___x_5078_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
v_isSharedCheck_5085_ = !lean_is_exclusive(v_l_5006_);
if (v_isSharedCheck_5085_ == 0)
{
lean_object* v_unused_5086_; lean_object* v_unused_5087_; lean_object* v_unused_5088_; lean_object* v_unused_5089_; lean_object* v_unused_5090_; 
v_unused_5086_ = lean_ctor_get(v_l_5006_, 4);
lean_dec(v_unused_5086_);
v_unused_5087_ = lean_ctor_get(v_l_5006_, 3);
lean_dec(v_unused_5087_);
v_unused_5088_ = lean_ctor_get(v_l_5006_, 2);
lean_dec(v_unused_5088_);
v_unused_5089_ = lean_ctor_get(v_l_5006_, 1);
lean_dec(v_unused_5089_);
v_unused_5090_ = lean_ctor_get(v_l_5006_, 0);
lean_dec(v_unused_5090_);
v___x_5080_ = v_l_5006_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_dec(v_l_5006_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 4, v_r_5020_);
lean_ctor_set(v___x_5080_, 3, v___x_5078_);
lean_ctor_set(v___x_5080_, 2, v_v_5018_);
lean_ctor_set(v___x_5080_, 1, v_k_5017_);
lean_ctor_set(v___x_5080_, 0, v___x_5075_);
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5075_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v_k_5017_);
lean_ctor_set(v_reuseFailAlloc_5084_, 2, v_v_5018_);
lean_ctor_set(v_reuseFailAlloc_5084_, 3, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5084_, 4, v_r_5020_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5098_; 
v_l_5098_ = lean_ctor_get(v_impl_5013_, 3);
lean_inc(v_l_5098_);
if (lean_obj_tag(v_l_5098_) == 0)
{
lean_object* v_r_5099_; lean_object* v_k_5100_; lean_object* v_v_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5124_; 
v_r_5099_ = lean_ctor_get(v_impl_5013_, 4);
v_k_5100_ = lean_ctor_get(v_impl_5013_, 1);
v_v_5101_ = lean_ctor_get(v_impl_5013_, 2);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_impl_5013_);
if (v_isSharedCheck_5124_ == 0)
{
lean_object* v_unused_5125_; lean_object* v_unused_5126_; 
v_unused_5125_ = lean_ctor_get(v_impl_5013_, 3);
lean_dec(v_unused_5125_);
v_unused_5126_ = lean_ctor_get(v_impl_5013_, 0);
lean_dec(v_unused_5126_);
v___x_5103_ = v_impl_5013_;
v_isShared_5104_ = v_isSharedCheck_5124_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_r_5099_);
lean_inc(v_v_5101_);
lean_inc(v_k_5100_);
lean_dec(v_impl_5013_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5124_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v_k_5105_; lean_object* v_v_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5120_; 
v_k_5105_ = lean_ctor_get(v_l_5098_, 1);
v_v_5106_ = lean_ctor_get(v_l_5098_, 2);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_l_5098_);
if (v_isSharedCheck_5120_ == 0)
{
lean_object* v_unused_5121_; lean_object* v_unused_5122_; lean_object* v_unused_5123_; 
v_unused_5121_ = lean_ctor_get(v_l_5098_, 4);
lean_dec(v_unused_5121_);
v_unused_5122_ = lean_ctor_get(v_l_5098_, 3);
lean_dec(v_unused_5122_);
v_unused_5123_ = lean_ctor_get(v_l_5098_, 0);
lean_dec(v_unused_5123_);
v___x_5108_ = v_l_5098_;
v_isShared_5109_ = v_isSharedCheck_5120_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_v_5106_);
lean_inc(v_k_5105_);
lean_dec(v_l_5098_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5120_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5110_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5099_, 2);
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 4, v_r_5099_);
lean_ctor_set(v___x_5108_, 3, v_r_5099_);
lean_ctor_set(v___x_5108_, 2, v_v_5005_);
lean_ctor_set(v___x_5108_, 1, v_k_5004_);
lean_ctor_set(v___x_5108_, 0, v___x_5014_);
v___x_5112_ = v___x_5108_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5119_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5119_, 3, v_r_5099_);
lean_ctor_set(v_reuseFailAlloc_5119_, 4, v_r_5099_);
v___x_5112_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
lean_object* v___x_5114_; 
lean_inc(v_r_5099_);
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 3, v_r_5099_);
lean_ctor_set(v___x_5103_, 0, v___x_5014_);
v___x_5114_ = v___x_5103_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_k_5100_);
lean_ctor_set(v_reuseFailAlloc_5118_, 2, v_v_5101_);
lean_ctor_set(v_reuseFailAlloc_5118_, 3, v_r_5099_);
lean_ctor_set(v_reuseFailAlloc_5118_, 4, v_r_5099_);
v___x_5114_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
lean_object* v___x_5116_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v___x_5114_);
lean_ctor_set(v___x_5009_, 3, v___x_5112_);
lean_ctor_set(v___x_5009_, 2, v_v_5106_);
lean_ctor_set(v___x_5009_, 1, v_k_5105_);
lean_ctor_set(v___x_5009_, 0, v___x_5110_);
v___x_5116_ = v___x_5009_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5117_, 1, v_k_5105_);
lean_ctor_set(v_reuseFailAlloc_5117_, 2, v_v_5106_);
lean_ctor_set(v_reuseFailAlloc_5117_, 3, v___x_5112_);
lean_ctor_set(v_reuseFailAlloc_5117_, 4, v___x_5114_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
}
else
{
lean_object* v_r_5127_; 
v_r_5127_ = lean_ctor_get(v_impl_5013_, 4);
lean_inc(v_r_5127_);
if (lean_obj_tag(v_r_5127_) == 0)
{
lean_object* v_k_5128_; lean_object* v_v_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5140_; 
v_k_5128_ = lean_ctor_get(v_impl_5013_, 1);
v_v_5129_ = lean_ctor_get(v_impl_5013_, 2);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_impl_5013_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; lean_object* v_unused_5142_; lean_object* v_unused_5143_; 
v_unused_5141_ = lean_ctor_get(v_impl_5013_, 4);
lean_dec(v_unused_5141_);
v_unused_5142_ = lean_ctor_get(v_impl_5013_, 3);
lean_dec(v_unused_5142_);
v_unused_5143_ = lean_ctor_get(v_impl_5013_, 0);
lean_dec(v_unused_5143_);
v___x_5131_ = v_impl_5013_;
v_isShared_5132_ = v_isSharedCheck_5140_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_v_5129_);
lean_inc(v_k_5128_);
lean_dec(v_impl_5013_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5140_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5133_ = lean_unsigned_to_nat(3u);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 4, v_l_5098_);
lean_ctor_set(v___x_5131_, 2, v_v_5005_);
lean_ctor_set(v___x_5131_, 1, v_k_5004_);
lean_ctor_set(v___x_5131_, 0, v___x_5014_);
v___x_5135_ = v___x_5131_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5139_, 3, v_l_5098_);
lean_ctor_set(v_reuseFailAlloc_5139_, 4, v_l_5098_);
v___x_5135_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5137_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_r_5127_);
lean_ctor_set(v___x_5009_, 3, v___x_5135_);
lean_ctor_set(v___x_5009_, 2, v_v_5129_);
lean_ctor_set(v___x_5009_, 1, v_k_5128_);
lean_ctor_set(v___x_5009_, 0, v___x_5133_);
v___x_5137_ = v___x_5009_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5133_);
lean_ctor_set(v_reuseFailAlloc_5138_, 1, v_k_5128_);
lean_ctor_set(v_reuseFailAlloc_5138_, 2, v_v_5129_);
lean_ctor_set(v_reuseFailAlloc_5138_, 3, v___x_5135_);
lean_ctor_set(v_reuseFailAlloc_5138_, 4, v_r_5127_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
else
{
lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5144_ = lean_unsigned_to_nat(2u);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_impl_5013_);
lean_ctor_set(v___x_5009_, 3, v_r_5127_);
lean_ctor_set(v___x_5009_, 0, v___x_5144_);
v___x_5146_ = v___x_5009_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5144_);
lean_ctor_set(v_reuseFailAlloc_5147_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5147_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5147_, 3, v_r_5127_);
lean_ctor_set(v_reuseFailAlloc_5147_, 4, v_impl_5013_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
}
else
{
lean_object* v___x_5149_; 
lean_dec(v_v_5005_);
lean_dec(v_k_5004_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 2, v_v_5001_);
lean_ctor_set(v___x_5009_, 1, v_k_5000_);
v___x_5149_ = v___x_5009_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_size_5003_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_k_5000_);
lean_ctor_set(v_reuseFailAlloc_5150_, 2, v_v_5001_);
lean_ctor_set(v_reuseFailAlloc_5150_, 3, v_l_5006_);
lean_ctor_set(v_reuseFailAlloc_5150_, 4, v_r_5007_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
else
{
lean_object* v_impl_5151_; lean_object* v___x_5152_; 
lean_dec(v_size_5003_);
v_impl_5151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5000_, v_v_5001_, v_l_5006_);
v___x_5152_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5007_) == 0)
{
lean_object* v_size_5153_; lean_object* v_size_5154_; lean_object* v_k_5155_; lean_object* v_v_5156_; lean_object* v_l_5157_; lean_object* v_r_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; uint8_t v___x_5161_; 
v_size_5153_ = lean_ctor_get(v_r_5007_, 0);
v_size_5154_ = lean_ctor_get(v_impl_5151_, 0);
lean_inc(v_size_5154_);
v_k_5155_ = lean_ctor_get(v_impl_5151_, 1);
lean_inc(v_k_5155_);
v_v_5156_ = lean_ctor_get(v_impl_5151_, 2);
lean_inc(v_v_5156_);
v_l_5157_ = lean_ctor_get(v_impl_5151_, 3);
lean_inc(v_l_5157_);
v_r_5158_ = lean_ctor_get(v_impl_5151_, 4);
lean_inc(v_r_5158_);
v___x_5159_ = lean_unsigned_to_nat(3u);
v___x_5160_ = lean_nat_mul(v___x_5159_, v_size_5153_);
v___x_5161_ = lean_nat_dec_lt(v___x_5160_, v_size_5154_);
lean_dec(v___x_5160_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5165_; 
lean_dec(v_r_5158_);
lean_dec(v_l_5157_);
lean_dec(v_v_5156_);
lean_dec(v_k_5155_);
v___x_5162_ = lean_nat_add(v___x_5152_, v_size_5154_);
lean_dec(v_size_5154_);
v___x_5163_ = lean_nat_add(v___x_5162_, v_size_5153_);
lean_dec(v___x_5162_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 3, v_impl_5151_);
lean_ctor_set(v___x_5009_, 0, v___x_5163_);
v___x_5165_ = v___x_5009_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5163_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5166_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5166_, 3, v_impl_5151_);
lean_ctor_set(v_reuseFailAlloc_5166_, 4, v_r_5007_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
else
{
lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5232_; 
v_isSharedCheck_5232_ = !lean_is_exclusive(v_impl_5151_);
if (v_isSharedCheck_5232_ == 0)
{
lean_object* v_unused_5233_; lean_object* v_unused_5234_; lean_object* v_unused_5235_; lean_object* v_unused_5236_; lean_object* v_unused_5237_; 
v_unused_5233_ = lean_ctor_get(v_impl_5151_, 4);
lean_dec(v_unused_5233_);
v_unused_5234_ = lean_ctor_get(v_impl_5151_, 3);
lean_dec(v_unused_5234_);
v_unused_5235_ = lean_ctor_get(v_impl_5151_, 2);
lean_dec(v_unused_5235_);
v_unused_5236_ = lean_ctor_get(v_impl_5151_, 1);
lean_dec(v_unused_5236_);
v_unused_5237_ = lean_ctor_get(v_impl_5151_, 0);
lean_dec(v_unused_5237_);
v___x_5168_ = v_impl_5151_;
v_isShared_5169_ = v_isSharedCheck_5232_;
goto v_resetjp_5167_;
}
else
{
lean_dec(v_impl_5151_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5232_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v_size_5170_; lean_object* v_size_5171_; lean_object* v_k_5172_; lean_object* v_v_5173_; lean_object* v_l_5174_; lean_object* v_r_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; 
v_size_5170_ = lean_ctor_get(v_l_5157_, 0);
v_size_5171_ = lean_ctor_get(v_r_5158_, 0);
v_k_5172_ = lean_ctor_get(v_r_5158_, 1);
v_v_5173_ = lean_ctor_get(v_r_5158_, 2);
v_l_5174_ = lean_ctor_get(v_r_5158_, 3);
v_r_5175_ = lean_ctor_get(v_r_5158_, 4);
v___x_5176_ = lean_unsigned_to_nat(2u);
v___x_5177_ = lean_nat_mul(v___x_5176_, v_size_5170_);
v___x_5178_ = lean_nat_dec_lt(v_size_5171_, v___x_5177_);
lean_dec(v___x_5177_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5207_; 
lean_inc(v_r_5175_);
lean_inc(v_l_5174_);
lean_inc(v_v_5173_);
lean_inc(v_k_5172_);
v_isSharedCheck_5207_ = !lean_is_exclusive(v_r_5158_);
if (v_isSharedCheck_5207_ == 0)
{
lean_object* v_unused_5208_; lean_object* v_unused_5209_; lean_object* v_unused_5210_; lean_object* v_unused_5211_; lean_object* v_unused_5212_; 
v_unused_5208_ = lean_ctor_get(v_r_5158_, 4);
lean_dec(v_unused_5208_);
v_unused_5209_ = lean_ctor_get(v_r_5158_, 3);
lean_dec(v_unused_5209_);
v_unused_5210_ = lean_ctor_get(v_r_5158_, 2);
lean_dec(v_unused_5210_);
v_unused_5211_ = lean_ctor_get(v_r_5158_, 1);
lean_dec(v_unused_5211_);
v_unused_5212_ = lean_ctor_get(v_r_5158_, 0);
lean_dec(v_unused_5212_);
v___x_5180_ = v_r_5158_;
v_isShared_5181_ = v_isSharedCheck_5207_;
goto v_resetjp_5179_;
}
else
{
lean_dec(v_r_5158_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5207_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___y_5185_; lean_object* v___y_5186_; lean_object* v___y_5187_; lean_object* v___x_5195_; lean_object* v___y_5197_; 
v___x_5182_ = lean_nat_add(v___x_5152_, v_size_5154_);
lean_dec(v_size_5154_);
v___x_5183_ = lean_nat_add(v___x_5182_, v_size_5153_);
lean_dec(v___x_5182_);
v___x_5195_ = lean_nat_add(v___x_5152_, v_size_5170_);
if (lean_obj_tag(v_l_5174_) == 0)
{
lean_object* v_size_5205_; 
v_size_5205_ = lean_ctor_get(v_l_5174_, 0);
lean_inc(v_size_5205_);
v___y_5197_ = v_size_5205_;
goto v___jp_5196_;
}
else
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_unsigned_to_nat(0u);
v___y_5197_ = v___x_5206_;
goto v___jp_5196_;
}
v___jp_5184_:
{
lean_object* v___x_5188_; lean_object* v___x_5190_; 
v___x_5188_ = lean_nat_add(v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec(v___y_5186_);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 4, v_r_5007_);
lean_ctor_set(v___x_5180_, 3, v_r_5175_);
lean_ctor_set(v___x_5180_, 2, v_v_5005_);
lean_ctor_set(v___x_5180_, 1, v_k_5004_);
lean_ctor_set(v___x_5180_, 0, v___x_5188_);
v___x_5190_ = v___x_5180_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5188_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5194_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5194_, 3, v_r_5175_);
lean_ctor_set(v_reuseFailAlloc_5194_, 4, v_r_5007_);
v___x_5190_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
lean_object* v___x_5192_; 
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 4, v___x_5190_);
lean_ctor_set(v___x_5168_, 3, v___y_5185_);
lean_ctor_set(v___x_5168_, 2, v_v_5173_);
lean_ctor_set(v___x_5168_, 1, v_k_5172_);
lean_ctor_set(v___x_5168_, 0, v___x_5183_);
v___x_5192_ = v___x_5168_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v_k_5172_);
lean_ctor_set(v_reuseFailAlloc_5193_, 2, v_v_5173_);
lean_ctor_set(v_reuseFailAlloc_5193_, 3, v___y_5185_);
lean_ctor_set(v_reuseFailAlloc_5193_, 4, v___x_5190_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
v___jp_5196_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = lean_nat_add(v___x_5195_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec(v___x_5195_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_l_5174_);
lean_ctor_set(v___x_5009_, 3, v_l_5157_);
lean_ctor_set(v___x_5009_, 2, v_v_5156_);
lean_ctor_set(v___x_5009_, 1, v_k_5155_);
lean_ctor_set(v___x_5009_, 0, v___x_5198_);
v___x_5200_ = v___x_5009_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5198_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_k_5155_);
lean_ctor_set(v_reuseFailAlloc_5204_, 2, v_v_5156_);
lean_ctor_set(v_reuseFailAlloc_5204_, 3, v_l_5157_);
lean_ctor_set(v_reuseFailAlloc_5204_, 4, v_l_5174_);
v___x_5200_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_nat_add(v___x_5152_, v_size_5153_);
if (lean_obj_tag(v_r_5175_) == 0)
{
lean_object* v_size_5202_; 
v_size_5202_ = lean_ctor_get(v_r_5175_, 0);
lean_inc(v_size_5202_);
v___y_5185_ = v___x_5200_;
v___y_5186_ = v___x_5201_;
v___y_5187_ = v_size_5202_;
goto v___jp_5184_;
}
else
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_unsigned_to_nat(0u);
v___y_5185_ = v___x_5200_;
v___y_5186_ = v___x_5201_;
v___y_5187_ = v___x_5203_;
goto v___jp_5184_;
}
}
}
}
}
else
{
lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5218_; 
lean_del_object(v___x_5009_);
v___x_5213_ = lean_nat_add(v___x_5152_, v_size_5154_);
lean_dec(v_size_5154_);
v___x_5214_ = lean_nat_add(v___x_5213_, v_size_5153_);
lean_dec(v___x_5213_);
v___x_5215_ = lean_nat_add(v___x_5152_, v_size_5153_);
v___x_5216_ = lean_nat_add(v___x_5215_, v_size_5171_);
lean_dec(v___x_5215_);
lean_inc_ref(v_r_5007_);
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 4, v_r_5007_);
lean_ctor_set(v___x_5168_, 3, v_r_5158_);
lean_ctor_set(v___x_5168_, 2, v_v_5005_);
lean_ctor_set(v___x_5168_, 1, v_k_5004_);
lean_ctor_set(v___x_5168_, 0, v___x_5216_);
v___x_5218_ = v___x_5168_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5231_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5231_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5231_, 3, v_r_5158_);
lean_ctor_set(v_reuseFailAlloc_5231_, 4, v_r_5007_);
v___x_5218_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
v_isSharedCheck_5225_ = !lean_is_exclusive(v_r_5007_);
if (v_isSharedCheck_5225_ == 0)
{
lean_object* v_unused_5226_; lean_object* v_unused_5227_; lean_object* v_unused_5228_; lean_object* v_unused_5229_; lean_object* v_unused_5230_; 
v_unused_5226_ = lean_ctor_get(v_r_5007_, 4);
lean_dec(v_unused_5226_);
v_unused_5227_ = lean_ctor_get(v_r_5007_, 3);
lean_dec(v_unused_5227_);
v_unused_5228_ = lean_ctor_get(v_r_5007_, 2);
lean_dec(v_unused_5228_);
v_unused_5229_ = lean_ctor_get(v_r_5007_, 1);
lean_dec(v_unused_5229_);
v_unused_5230_ = lean_ctor_get(v_r_5007_, 0);
lean_dec(v_unused_5230_);
v___x_5220_ = v_r_5007_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_dec(v_r_5007_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 4, v___x_5218_);
lean_ctor_set(v___x_5220_, 3, v_l_5157_);
lean_ctor_set(v___x_5220_, 2, v_v_5156_);
lean_ctor_set(v___x_5220_, 1, v_k_5155_);
lean_ctor_set(v___x_5220_, 0, v___x_5214_);
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5214_);
lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_k_5155_);
lean_ctor_set(v_reuseFailAlloc_5224_, 2, v_v_5156_);
lean_ctor_set(v_reuseFailAlloc_5224_, 3, v_l_5157_);
lean_ctor_set(v_reuseFailAlloc_5224_, 4, v___x_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5238_; 
v_l_5238_ = lean_ctor_get(v_impl_5151_, 3);
lean_inc(v_l_5238_);
if (lean_obj_tag(v_l_5238_) == 0)
{
lean_object* v_r_5239_; lean_object* v_k_5240_; lean_object* v_v_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5252_; 
v_r_5239_ = lean_ctor_get(v_impl_5151_, 4);
v_k_5240_ = lean_ctor_get(v_impl_5151_, 1);
v_v_5241_ = lean_ctor_get(v_impl_5151_, 2);
v_isSharedCheck_5252_ = !lean_is_exclusive(v_impl_5151_);
if (v_isSharedCheck_5252_ == 0)
{
lean_object* v_unused_5253_; lean_object* v_unused_5254_; 
v_unused_5253_ = lean_ctor_get(v_impl_5151_, 3);
lean_dec(v_unused_5253_);
v_unused_5254_ = lean_ctor_get(v_impl_5151_, 0);
lean_dec(v_unused_5254_);
v___x_5243_ = v_impl_5151_;
v_isShared_5244_ = v_isSharedCheck_5252_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_r_5239_);
lean_inc(v_v_5241_);
lean_inc(v_k_5240_);
lean_dec(v_impl_5151_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5252_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5245_; lean_object* v___x_5247_; 
v___x_5245_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5239_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 3, v_r_5239_);
lean_ctor_set(v___x_5243_, 2, v_v_5005_);
lean_ctor_set(v___x_5243_, 1, v_k_5004_);
lean_ctor_set(v___x_5243_, 0, v___x_5152_);
v___x_5247_ = v___x_5243_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5152_);
lean_ctor_set(v_reuseFailAlloc_5251_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5251_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5251_, 3, v_r_5239_);
lean_ctor_set(v_reuseFailAlloc_5251_, 4, v_r_5239_);
v___x_5247_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5249_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v___x_5247_);
lean_ctor_set(v___x_5009_, 3, v_l_5238_);
lean_ctor_set(v___x_5009_, 2, v_v_5241_);
lean_ctor_set(v___x_5009_, 1, v_k_5240_);
lean_ctor_set(v___x_5009_, 0, v___x_5245_);
v___x_5249_ = v___x_5009_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5250_, 1, v_k_5240_);
lean_ctor_set(v_reuseFailAlloc_5250_, 2, v_v_5241_);
lean_ctor_set(v_reuseFailAlloc_5250_, 3, v_l_5238_);
lean_ctor_set(v_reuseFailAlloc_5250_, 4, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
}
else
{
lean_object* v_r_5255_; 
v_r_5255_ = lean_ctor_get(v_impl_5151_, 4);
lean_inc(v_r_5255_);
if (lean_obj_tag(v_r_5255_) == 0)
{
lean_object* v_k_5256_; lean_object* v_v_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5280_; 
v_k_5256_ = lean_ctor_get(v_impl_5151_, 1);
v_v_5257_ = lean_ctor_get(v_impl_5151_, 2);
v_isSharedCheck_5280_ = !lean_is_exclusive(v_impl_5151_);
if (v_isSharedCheck_5280_ == 0)
{
lean_object* v_unused_5281_; lean_object* v_unused_5282_; lean_object* v_unused_5283_; 
v_unused_5281_ = lean_ctor_get(v_impl_5151_, 4);
lean_dec(v_unused_5281_);
v_unused_5282_ = lean_ctor_get(v_impl_5151_, 3);
lean_dec(v_unused_5282_);
v_unused_5283_ = lean_ctor_get(v_impl_5151_, 0);
lean_dec(v_unused_5283_);
v___x_5259_ = v_impl_5151_;
v_isShared_5260_ = v_isSharedCheck_5280_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_v_5257_);
lean_inc(v_k_5256_);
lean_dec(v_impl_5151_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5280_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v_k_5261_; lean_object* v_v_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5276_; 
v_k_5261_ = lean_ctor_get(v_r_5255_, 1);
v_v_5262_ = lean_ctor_get(v_r_5255_, 2);
v_isSharedCheck_5276_ = !lean_is_exclusive(v_r_5255_);
if (v_isSharedCheck_5276_ == 0)
{
lean_object* v_unused_5277_; lean_object* v_unused_5278_; lean_object* v_unused_5279_; 
v_unused_5277_ = lean_ctor_get(v_r_5255_, 4);
lean_dec(v_unused_5277_);
v_unused_5278_ = lean_ctor_get(v_r_5255_, 3);
lean_dec(v_unused_5278_);
v_unused_5279_ = lean_ctor_get(v_r_5255_, 0);
lean_dec(v_unused_5279_);
v___x_5264_ = v_r_5255_;
v_isShared_5265_ = v_isSharedCheck_5276_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_v_5262_);
lean_inc(v_k_5261_);
lean_dec(v_r_5255_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5276_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5266_; lean_object* v___x_5268_; 
v___x_5266_ = lean_unsigned_to_nat(3u);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 4, v_l_5238_);
lean_ctor_set(v___x_5264_, 3, v_l_5238_);
lean_ctor_set(v___x_5264_, 2, v_v_5257_);
lean_ctor_set(v___x_5264_, 1, v_k_5256_);
lean_ctor_set(v___x_5264_, 0, v___x_5152_);
v___x_5268_ = v___x_5264_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5152_);
lean_ctor_set(v_reuseFailAlloc_5275_, 1, v_k_5256_);
lean_ctor_set(v_reuseFailAlloc_5275_, 2, v_v_5257_);
lean_ctor_set(v_reuseFailAlloc_5275_, 3, v_l_5238_);
lean_ctor_set(v_reuseFailAlloc_5275_, 4, v_l_5238_);
v___x_5268_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
lean_object* v___x_5270_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 4, v_l_5238_);
lean_ctor_set(v___x_5259_, 2, v_v_5005_);
lean_ctor_set(v___x_5259_, 1, v_k_5004_);
lean_ctor_set(v___x_5259_, 0, v___x_5152_);
v___x_5270_ = v___x_5259_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5152_);
lean_ctor_set(v_reuseFailAlloc_5274_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5274_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5274_, 3, v_l_5238_);
lean_ctor_set(v_reuseFailAlloc_5274_, 4, v_l_5238_);
v___x_5270_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5272_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v___x_5270_);
lean_ctor_set(v___x_5009_, 3, v___x_5268_);
lean_ctor_set(v___x_5009_, 2, v_v_5262_);
lean_ctor_set(v___x_5009_, 1, v_k_5261_);
lean_ctor_set(v___x_5009_, 0, v___x_5266_);
v___x_5272_ = v___x_5009_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5266_);
lean_ctor_set(v_reuseFailAlloc_5273_, 1, v_k_5261_);
lean_ctor_set(v_reuseFailAlloc_5273_, 2, v_v_5262_);
lean_ctor_set(v_reuseFailAlloc_5273_, 3, v___x_5268_);
lean_ctor_set(v_reuseFailAlloc_5273_, 4, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
}
}
else
{
lean_object* v___x_5284_; lean_object* v___x_5286_; 
v___x_5284_ = lean_unsigned_to_nat(2u);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 4, v_r_5255_);
lean_ctor_set(v___x_5009_, 3, v_impl_5151_);
lean_ctor_set(v___x_5009_, 0, v___x_5284_);
v___x_5286_ = v___x_5009_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v_v_5005_);
lean_ctor_set(v_reuseFailAlloc_5287_, 3, v_impl_5151_);
lean_ctor_set(v_reuseFailAlloc_5287_, 4, v_r_5255_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = lean_unsigned_to_nat(1u);
v___x_5290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
lean_ctor_set(v___x_5290_, 1, v_k_5000_);
lean_ctor_set(v___x_5290_, 2, v_v_5001_);
lean_ctor_set(v___x_5290_, 3, v_t_5002_);
lean_ctor_set(v___x_5290_, 4, v_t_5002_);
return v___x_5290_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5291_, lean_object* v_t_5292_){
_start:
{
if (lean_obj_tag(v_t_5292_) == 0)
{
lean_object* v_k_5293_; lean_object* v_l_5294_; lean_object* v_r_5295_; uint8_t v___x_5296_; 
v_k_5293_ = lean_ctor_get(v_t_5292_, 1);
v_l_5294_ = lean_ctor_get(v_t_5292_, 3);
v_r_5295_ = lean_ctor_get(v_t_5292_, 4);
v___x_5296_ = lean_nat_dec_lt(v_k_5293_, v_k_5291_);
if (v___x_5296_ == 0)
{
uint8_t v___x_5297_; 
v___x_5297_ = lean_nat_dec_eq(v_k_5293_, v_k_5291_);
if (v___x_5297_ == 0)
{
v_t_5292_ = v_r_5295_;
goto _start;
}
else
{
return v___x_5297_;
}
}
else
{
v_t_5292_ = v_l_5294_;
goto _start;
}
}
else
{
uint8_t v___x_5300_; 
v___x_5300_ = 0;
return v___x_5300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5301_, lean_object* v_t_5302_){
_start:
{
uint8_t v_res_5303_; lean_object* v_r_5304_; 
v_res_5303_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5301_, v_t_5302_);
lean_dec(v_t_5302_);
lean_dec(v_k_5301_);
v_r_5304_ = lean_box(v_res_5303_);
return v_r_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5305_, lean_object* v_e_5306_){
_start:
{
lean_object* v_defaultInstances_5307_; lean_object* v_priorities_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5335_; 
v_defaultInstances_5307_ = lean_ctor_get(v_d_5305_, 0);
v_priorities_5308_ = lean_ctor_get(v_d_5305_, 1);
v_isSharedCheck_5335_ = !lean_is_exclusive(v_d_5305_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5310_ = v_d_5305_;
v_isShared_5311_ = v_isSharedCheck_5335_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_priorities_5308_);
lean_inc(v_defaultInstances_5307_);
lean_dec(v_d_5305_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5335_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v_className_5312_; lean_object* v_instanceName_5313_; lean_object* v_priority_5314_; lean_object* v___y_5316_; uint8_t v___x_5332_; 
v_className_5312_ = lean_ctor_get(v_e_5306_, 0);
lean_inc(v_className_5312_);
v_instanceName_5313_ = lean_ctor_get(v_e_5306_, 1);
lean_inc(v_instanceName_5313_);
v_priority_5314_ = lean_ctor_get(v_e_5306_, 2);
lean_inc(v_priority_5314_);
lean_dec_ref(v_e_5306_);
v___x_5332_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5314_, v_priorities_5308_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5333_ = lean_box(0);
lean_inc(v_priority_5314_);
v___x_5334_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5314_, v___x_5333_, v_priorities_5308_);
v___y_5316_ = v___x_5334_;
goto v___jp_5315_;
}
else
{
v___y_5316_ = v_priorities_5308_;
goto v___jp_5315_;
}
v___jp_5315_:
{
lean_object* v___x_5317_; 
v___x_5317_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5307_, v_className_5312_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5318_, 0, v_instanceName_5313_);
lean_ctor_set(v___x_5318_, 1, v_priority_5314_);
v___x_5319_ = lean_box(0);
v___x_5320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5318_);
lean_ctor_set(v___x_5320_, 1, v___x_5319_);
v___x_5321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5312_, v___x_5320_, v_defaultInstances_5307_);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 1, v___y_5316_);
lean_ctor_set(v___x_5310_, 0, v___x_5321_);
v___x_5323_ = v___x_5310_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v___y_5316_);
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
lean_object* v_val_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
v_val_5325_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_val_5325_);
lean_dec_ref(v___x_5317_);
v___x_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5326_, 0, v_instanceName_5313_);
lean_ctor_set(v___x_5326_, 1, v_priority_5314_);
v___x_5327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
lean_ctor_set(v___x_5327_, 1, v_val_5325_);
v___x_5328_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5312_, v___x_5327_, v_defaultInstances_5307_);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 1, v___y_5316_);
lean_ctor_set(v___x_5310_, 0, v___x_5328_);
v___x_5330_ = v___x_5310_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
lean_ctor_set(v_reuseFailAlloc_5331_, 1, v___y_5316_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5336_, lean_object* v_k_5337_, lean_object* v_t_5338_){
_start:
{
uint8_t v___x_5339_; 
v___x_5339_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5337_, v_t_5338_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5340_, lean_object* v_k_5341_, lean_object* v_t_5342_){
_start:
{
uint8_t v_res_5343_; lean_object* v_r_5344_; 
v_res_5343_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5340_, v_k_5341_, v_t_5342_);
lean_dec(v_t_5342_);
lean_dec(v_k_5341_);
v_r_5344_ = lean_box(v_res_5343_);
return v_r_5344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5345_, lean_object* v_k_5346_, lean_object* v_v_5347_, lean_object* v_t_5348_, lean_object* v_hl_5349_){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5346_, v_v_5347_, v_t_5348_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5351_){
_start:
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_array_mk(v_es_5351_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5353_, size_t v_i_5354_, size_t v_stop_5355_, lean_object* v_b_5356_){
_start:
{
uint8_t v___x_5357_; 
v___x_5357_ = lean_usize_dec_eq(v_i_5354_, v_stop_5355_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; lean_object* v___x_5359_; size_t v___x_5360_; size_t v___x_5361_; 
v___x_5358_ = lean_array_uget_borrowed(v_as_5353_, v_i_5354_);
lean_inc(v___x_5358_);
v___x_5359_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5356_, v___x_5358_);
v___x_5360_ = ((size_t)1ULL);
v___x_5361_ = lean_usize_add(v_i_5354_, v___x_5360_);
v_i_5354_ = v___x_5361_;
v_b_5356_ = v___x_5359_;
goto _start;
}
else
{
return v_b_5356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5363_, lean_object* v_i_5364_, lean_object* v_stop_5365_, lean_object* v_b_5366_){
_start:
{
size_t v_i_boxed_5367_; size_t v_stop_boxed_5368_; lean_object* v_res_5369_; 
v_i_boxed_5367_ = lean_unbox_usize(v_i_5364_);
lean_dec(v_i_5364_);
v_stop_boxed_5368_ = lean_unbox_usize(v_stop_5365_);
lean_dec(v_stop_5365_);
v_res_5369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_5363_, v_i_boxed_5367_, v_stop_boxed_5368_, v_b_5366_);
lean_dec_ref(v_as_5363_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_5370_, size_t v_i_5371_, size_t v_stop_5372_, lean_object* v_b_5373_){
_start:
{
lean_object* v___y_5375_; uint8_t v___x_5379_; 
v___x_5379_ = lean_usize_dec_eq(v_i_5371_, v_stop_5372_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; uint8_t v___x_5383_; 
v___x_5380_ = lean_array_uget_borrowed(v_as_5370_, v_i_5371_);
v___x_5381_ = lean_unsigned_to_nat(0u);
v___x_5382_ = lean_array_get_size(v___x_5380_);
v___x_5383_ = lean_nat_dec_lt(v___x_5381_, v___x_5382_);
if (v___x_5383_ == 0)
{
v___y_5375_ = v_b_5373_;
goto v___jp_5374_;
}
else
{
uint8_t v___x_5384_; 
v___x_5384_ = lean_nat_dec_le(v___x_5382_, v___x_5382_);
if (v___x_5384_ == 0)
{
if (v___x_5383_ == 0)
{
v___y_5375_ = v_b_5373_;
goto v___jp_5374_;
}
else
{
size_t v___x_5385_; size_t v___x_5386_; lean_object* v___x_5387_; 
v___x_5385_ = ((size_t)0ULL);
v___x_5386_ = lean_usize_of_nat(v___x_5382_);
v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5380_, v___x_5385_, v___x_5386_, v_b_5373_);
v___y_5375_ = v___x_5387_;
goto v___jp_5374_;
}
}
else
{
size_t v___x_5388_; size_t v___x_5389_; lean_object* v___x_5390_; 
v___x_5388_ = ((size_t)0ULL);
v___x_5389_ = lean_usize_of_nat(v___x_5382_);
v___x_5390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5380_, v___x_5388_, v___x_5389_, v_b_5373_);
v___y_5375_ = v___x_5390_;
goto v___jp_5374_;
}
}
}
else
{
return v_b_5373_;
}
v___jp_5374_:
{
size_t v___x_5376_; size_t v___x_5377_; 
v___x_5376_ = ((size_t)1ULL);
v___x_5377_ = lean_usize_add(v_i_5371_, v___x_5376_);
v_i_5371_ = v___x_5377_;
v_b_5373_ = v___y_5375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5391_, lean_object* v_i_5392_, lean_object* v_stop_5393_, lean_object* v_b_5394_){
_start:
{
size_t v_i_boxed_5395_; size_t v_stop_boxed_5396_; lean_object* v_res_5397_; 
v_i_boxed_5395_ = lean_unbox_usize(v_i_5392_);
lean_dec(v_i_5392_);
v_stop_boxed_5396_ = lean_unbox_usize(v_stop_5393_);
lean_dec(v_stop_5393_);
v_res_5397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5391_, v_i_boxed_5395_, v_stop_boxed_5396_, v_b_5394_);
lean_dec_ref(v_as_5391_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5398_, lean_object* v_as_5399_){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; uint8_t v___x_5402_; 
v___x_5400_ = lean_unsigned_to_nat(0u);
v___x_5401_ = lean_array_get_size(v_as_5399_);
v___x_5402_ = lean_nat_dec_lt(v___x_5400_, v___x_5401_);
if (v___x_5402_ == 0)
{
return v_initState_5398_;
}
else
{
uint8_t v___x_5403_; 
v___x_5403_ = lean_nat_dec_le(v___x_5401_, v___x_5401_);
if (v___x_5403_ == 0)
{
if (v___x_5402_ == 0)
{
return v_initState_5398_;
}
else
{
size_t v___x_5404_; size_t v___x_5405_; lean_object* v___x_5406_; 
v___x_5404_ = ((size_t)0ULL);
v___x_5405_ = lean_usize_of_nat(v___x_5401_);
v___x_5406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5399_, v___x_5404_, v___x_5405_, v_initState_5398_);
return v___x_5406_;
}
}
else
{
size_t v___x_5407_; size_t v___x_5408_; lean_object* v___x_5409_; 
v___x_5407_ = ((size_t)0ULL);
v___x_5408_ = lean_usize_of_nat(v___x_5401_);
v___x_5409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5399_, v___x_5407_, v___x_5408_, v_initState_5398_);
return v___x_5409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5410_, lean_object* v_as_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5410_, v_as_5411_);
lean_dec_ref(v_as_5411_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5413_){
_start:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5414_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5415_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5414_, v_es_5413_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5416_);
lean_dec_ref(v_es_5416_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5434_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5435_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5434_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___x_5442_; lean_object* v_nextMacroScope_5443_; lean_object* v_ngen_5444_; lean_object* v_auxDeclNGen_5445_; lean_object* v_traceState_5446_; lean_object* v_messages_5447_; lean_object* v_infoState_5448_; lean_object* v_snapshotTasks_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5475_; 
v___x_5442_ = lean_st_ref_take(v___y_5440_);
v_nextMacroScope_5443_ = lean_ctor_get(v___x_5442_, 1);
v_ngen_5444_ = lean_ctor_get(v___x_5442_, 2);
v_auxDeclNGen_5445_ = lean_ctor_get(v___x_5442_, 3);
v_traceState_5446_ = lean_ctor_get(v___x_5442_, 4);
v_messages_5447_ = lean_ctor_get(v___x_5442_, 6);
v_infoState_5448_ = lean_ctor_get(v___x_5442_, 7);
v_snapshotTasks_5449_ = lean_ctor_get(v___x_5442_, 8);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5475_ == 0)
{
lean_object* v_unused_5476_; lean_object* v_unused_5477_; 
v_unused_5476_ = lean_ctor_get(v___x_5442_, 5);
lean_dec(v_unused_5476_);
v_unused_5477_ = lean_ctor_get(v___x_5442_, 0);
lean_dec(v_unused_5477_);
v___x_5451_ = v___x_5442_;
v_isShared_5452_ = v_isSharedCheck_5475_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_snapshotTasks_5449_);
lean_inc(v_infoState_5448_);
lean_inc(v_messages_5447_);
lean_inc(v_traceState_5446_);
lean_inc(v_auxDeclNGen_5445_);
lean_inc(v_ngen_5444_);
lean_inc(v_nextMacroScope_5443_);
lean_dec(v___x_5442_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5475_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
v___x_5453_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 5, v___x_5453_);
lean_ctor_set(v___x_5451_, 0, v_env_5438_);
v___x_5455_ = v___x_5451_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_env_5438_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_nextMacroScope_5443_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v_ngen_5444_);
lean_ctor_set(v_reuseFailAlloc_5474_, 3, v_auxDeclNGen_5445_);
lean_ctor_set(v_reuseFailAlloc_5474_, 4, v_traceState_5446_);
lean_ctor_set(v_reuseFailAlloc_5474_, 5, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5474_, 6, v_messages_5447_);
lean_ctor_set(v_reuseFailAlloc_5474_, 7, v_infoState_5448_);
lean_ctor_set(v_reuseFailAlloc_5474_, 8, v_snapshotTasks_5449_);
v___x_5455_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v_mctx_5458_; lean_object* v_zetaDeltaFVarIds_5459_; lean_object* v_postponed_5460_; lean_object* v_diag_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5472_; 
v___x_5456_ = lean_st_ref_set(v___y_5440_, v___x_5455_);
v___x_5457_ = lean_st_ref_take(v___y_5439_);
v_mctx_5458_ = lean_ctor_get(v___x_5457_, 0);
v_zetaDeltaFVarIds_5459_ = lean_ctor_get(v___x_5457_, 2);
v_postponed_5460_ = lean_ctor_get(v___x_5457_, 3);
v_diag_5461_ = lean_ctor_get(v___x_5457_, 4);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5457_);
if (v_isSharedCheck_5472_ == 0)
{
lean_object* v_unused_5473_; 
v_unused_5473_ = lean_ctor_get(v___x_5457_, 1);
lean_dec(v_unused_5473_);
v___x_5463_ = v___x_5457_;
v_isShared_5464_ = v_isSharedCheck_5472_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_diag_5461_);
lean_inc(v_postponed_5460_);
lean_inc(v_zetaDeltaFVarIds_5459_);
lean_inc(v_mctx_5458_);
lean_dec(v___x_5457_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5472_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5465_; lean_object* v___x_5467_; 
v___x_5465_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 1, v___x_5465_);
v___x_5467_ = v___x_5463_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_mctx_5458_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v___x_5465_);
lean_ctor_set(v_reuseFailAlloc_5471_, 2, v_zetaDeltaFVarIds_5459_);
lean_ctor_set(v_reuseFailAlloc_5471_, 3, v_postponed_5460_);
lean_ctor_set(v_reuseFailAlloc_5471_, 4, v_diag_5461_);
v___x_5467_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5468_ = lean_st_ref_set(v___y_5439_, v___x_5467_);
v___x_5469_ = lean_box(0);
v___x_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5469_);
return v___x_5470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5478_, v___y_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v___x_5489_; 
v___x_5489_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5483_, v___y_5485_, v___y_5487_);
return v___x_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
lean_dec(v___y_5494_);
lean_dec_ref(v___y_5493_);
lean_dec(v___y_5492_);
lean_dec_ref(v___y_5491_);
return v_res_5496_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5498_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5499_ = l_Lean_stringToMessageData(v___x_5498_);
return v___x_5499_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5501_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5502_ = l_Lean_stringToMessageData(v___x_5501_);
return v___x_5502_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5504_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5505_ = l_Lean_stringToMessageData(v___x_5504_);
return v___x_5505_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; 
v___x_5507_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5508_ = l_Lean_stringToMessageData(v___x_5507_);
return v___x_5508_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5511_ = l_Lean_stringToMessageData(v___x_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5512_, lean_object* v_prio_5513_, lean_object* v_x_5514_, lean_object* v_type_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_){
_start:
{
lean_object* v___x_5521_; 
v___x_5521_ = l_Lean_Expr_getAppFn(v_type_5515_);
if (lean_obj_tag(v___x_5521_) == 4)
{
lean_object* v_declName_5522_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___x_5537_; lean_object* v_env_5538_; uint8_t v___x_5539_; 
v_declName_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc_n(v_declName_5522_, 2);
lean_dec_ref(v___x_5521_);
v___x_5537_ = lean_st_ref_get(v___y_5519_);
v_env_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc_ref(v_env_5538_);
lean_dec(v___x_5537_);
v___x_5539_ = lean_is_class(v_env_5538_, v_declName_5522_);
if (v___x_5539_ == 0)
{
lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
lean_dec(v_prio_5513_);
v___x_5540_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5541_ = l_Lean_MessageData_ofConstName(v_declName_5512_, v___x_5539_);
v___x_5542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5540_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
lean_inc(v_declName_5522_);
v___x_5545_ = l_Lean_MessageData_ofName(v_declName_5522_);
v___x_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5544_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5546_);
lean_ctor_set(v___x_5548_, 1, v___x_5547_);
v___x_5549_ = l_Lean_MessageData_ofConstName(v_declName_5522_, v___x_5539_);
v___x_5550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5548_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5552_, 0, v___x_5550_);
lean_ctor_set(v___x_5552_, 1, v___x_5551_);
v___x_5553_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5552_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
return v___x_5553_;
}
else
{
v___y_5524_ = v___y_5516_;
v___y_5525_ = v___y_5517_;
v___y_5526_ = v___y_5518_;
v___y_5527_ = v___y_5519_;
goto v___jp_5523_;
}
v___jp_5523_:
{
lean_object* v___x_5528_; lean_object* v_env_5529_; lean_object* v___x_5530_; lean_object* v_toEnvExtension_5531_; lean_object* v_asyncMode_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
v___x_5528_ = lean_st_ref_get(v___y_5527_);
v_env_5529_ = lean_ctor_get(v___x_5528_, 0);
lean_inc_ref(v_env_5529_);
lean_dec(v___x_5528_);
v___x_5530_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5531_ = lean_ctor_get(v___x_5530_, 0);
v_asyncMode_5532_ = lean_ctor_get(v_toEnvExtension_5531_, 2);
v___x_5533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5533_, 0, v_declName_5522_);
lean_ctor_set(v___x_5533_, 1, v_declName_5512_);
lean_ctor_set(v___x_5533_, 2, v_prio_5513_);
v___x_5534_ = lean_box(0);
v___x_5535_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5530_, v_env_5529_, v___x_5533_, v_asyncMode_5532_, v___x_5534_);
v___x_5536_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5535_, v___y_5525_, v___y_5527_);
return v___x_5536_;
}
}
else
{
lean_object* v___x_5554_; uint8_t v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
lean_dec_ref(v___x_5521_);
lean_dec(v_prio_5513_);
v___x_5554_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5555_ = 0;
v___x_5556_ = l_Lean_MessageData_ofConstName(v_declName_5512_, v___x_5555_);
v___x_5557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5554_);
lean_ctor_set(v___x_5557_, 1, v___x_5556_);
v___x_5558_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5557_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
v___x_5560_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5559_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
return v___x_5560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5561_, lean_object* v_prio_5562_, lean_object* v_x_5563_, lean_object* v_type_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v_res_5570_; 
v_res_5570_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5561_, v_prio_5562_, v_x_5563_, v_type_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec(v___y_5566_);
lean_dec_ref(v___y_5565_);
lean_dec_ref(v_type_5564_);
lean_dec_ref(v_x_5563_);
return v_res_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5571_, lean_object* v_prio_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_){
_start:
{
lean_object* v___x_5578_; lean_object* v_env_5579_; uint8_t v___x_5580_; lean_object* v___x_5581_; 
v___x_5578_ = lean_st_ref_get(v_a_5576_);
v_env_5579_ = lean_ctor_get(v___x_5578_, 0);
lean_inc_ref(v_env_5579_);
lean_dec(v___x_5578_);
v___x_5580_ = 0;
lean_inc(v_declName_5571_);
v___x_5581_ = l_Lean_Environment_find_x3f(v_env_5579_, v_declName_5571_, v___x_5580_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
lean_dec(v_prio_5572_);
v___x_5582_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5583_ = l_Lean_MessageData_ofConstName(v_declName_5571_, v___x_5580_);
v___x_5584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5582_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5584_);
lean_ctor_set(v___x_5586_, 1, v___x_5585_);
v___x_5587_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5586_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_);
return v___x_5587_;
}
else
{
lean_object* v_val_5588_; lean_object* v___f_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v_val_5588_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_val_5588_);
lean_dec_ref(v___x_5581_);
v___f_5589_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5589_, 0, v_declName_5571_);
lean_closure_set(v___f_5589_, 1, v_prio_5572_);
v___x_5590_ = l_Lean_ConstantInfo_type(v_val_5588_);
lean_dec(v_val_5588_);
v___x_5591_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5590_, v___f_5589_, v___x_5580_, v___x_5580_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5592_, lean_object* v_prio_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l_Lean_Meta_addDefaultInstance(v_declName_5592_, v_prio_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_);
lean_dec(v_a_5597_);
lean_dec_ref(v_a_5596_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
return v_res_5599_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5601_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5602_ = l_Lean_stringToMessageData(v___x_5601_);
return v___x_5602_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5605_ = l_Lean_stringToMessageData(v___x_5604_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5609_, uint8_t v_kind_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_){
_start:
{
lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___y_5620_; 
v___x_5614_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5615_ = l_Lean_MessageData_ofName(v_name_5609_);
v___x_5616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5616_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
switch(v_kind_5610_)
{
case 0:
{
lean_object* v___x_5627_; 
v___x_5627_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5620_ = v___x_5627_;
goto v___jp_5619_;
}
case 1:
{
lean_object* v___x_5628_; 
v___x_5628_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5620_ = v___x_5628_;
goto v___jp_5619_;
}
default: 
{
lean_object* v___x_5629_; 
v___x_5629_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5620_ = v___x_5629_;
goto v___jp_5619_;
}
}
v___jp_5619_:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; 
lean_inc_ref(v___y_5620_);
v___x_5621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5621_, 0, v___y_5620_);
v___x_5622_ = l_Lean_MessageData_ofFormat(v___x_5621_);
v___x_5623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5618_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5625_, v___y_5611_, v___y_5612_);
return v___x_5626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5630_, lean_object* v_kind_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_){
_start:
{
uint8_t v_kind_boxed_5635_; lean_object* v_res_5636_; 
v_kind_boxed_5635_ = lean_unbox(v_kind_5631_);
v_res_5636_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5630_, v_kind_boxed_5635_, v___y_5632_, v___y_5633_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5637_, lean_object* v___x_5638_, lean_object* v___x_5639_, lean_object* v_declName_5640_, lean_object* v_stx_5641_, uint8_t v_kind_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5646_ = lean_unsigned_to_nat(1u);
v___x_5647_ = l_Lean_Syntax_getArg(v_stx_5641_, v___x_5646_);
v___x_5648_ = l_Lean_getAttrParamOptPrio(v___x_5647_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___y_5651_; lean_object* v___y_5652_; uint8_t v___x_5683_; uint8_t v___x_5684_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
lean_dec_ref(v___x_5648_);
v___x_5683_ = 0;
v___x_5684_ = l_Lean_instBEqAttributeKind_beq(v_kind_5642_, v___x_5683_);
if (v___x_5684_ == 0)
{
lean_object* v___x_5685_; 
lean_dec(v_a_5649_);
lean_dec(v_declName_5640_);
lean_dec(v___x_5638_);
lean_dec(v___x_5637_);
v___x_5685_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5639_, v_kind_5642_, v___y_5643_, v___y_5644_);
return v___x_5685_;
}
else
{
lean_dec(v___x_5639_);
v___y_5651_ = v___y_5643_;
v___y_5652_ = v___y_5644_;
goto v___jp_5650_;
}
v___jp_5650_:
{
uint8_t v___x_5653_; uint8_t v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; size_t v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; 
v___x_5653_ = 0;
v___x_5654_ = 1;
v___x_5655_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5656_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5657_ = lean_unsigned_to_nat(32u);
v___x_5658_ = lean_mk_empty_array_with_capacity(v___x_5657_);
v___x_5659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5660_ = ((size_t)5ULL);
lean_inc_n(v___x_5637_, 6);
v___x_5661_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5661_, 0, v___x_5659_);
lean_ctor_set(v___x_5661_, 1, v___x_5658_);
lean_ctor_set(v___x_5661_, 2, v___x_5637_);
lean_ctor_set(v___x_5661_, 3, v___x_5637_);
lean_ctor_set_usize(v___x_5661_, 4, v___x_5660_);
v___x_5662_ = lean_box(1);
lean_inc_ref(v___x_5661_);
v___x_5663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5656_);
lean_ctor_set(v___x_5663_, 1, v___x_5661_);
lean_ctor_set(v___x_5663_, 2, v___x_5662_);
v___x_5664_ = lean_mk_empty_array_with_capacity(v___x_5637_);
v___x_5665_ = lean_box(0);
lean_inc(v___x_5638_);
v___x_5666_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5666_, 0, v___x_5655_);
lean_ctor_set(v___x_5666_, 1, v___x_5638_);
lean_ctor_set(v___x_5666_, 2, v___x_5663_);
lean_ctor_set(v___x_5666_, 3, v___x_5664_);
lean_ctor_set(v___x_5666_, 4, v___x_5665_);
lean_ctor_set(v___x_5666_, 5, v___x_5637_);
lean_ctor_set(v___x_5666_, 6, v___x_5665_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*7, v___x_5653_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*7 + 1, v___x_5653_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*7 + 2, v___x_5653_);
lean_ctor_set_uint8(v___x_5666_, sizeof(void*)*7 + 3, v___x_5654_);
v___x_5667_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5637_);
lean_ctor_set(v___x_5667_, 1, v___x_5637_);
lean_ctor_set(v___x_5667_, 2, v___x_5637_);
lean_ctor_set(v___x_5667_, 3, v___x_5637_);
lean_ctor_set(v___x_5667_, 4, v___x_5656_);
lean_ctor_set(v___x_5667_, 5, v___x_5656_);
lean_ctor_set(v___x_5667_, 6, v___x_5656_);
lean_ctor_set(v___x_5667_, 7, v___x_5656_);
lean_ctor_set(v___x_5667_, 8, v___x_5656_);
lean_ctor_set(v___x_5667_, 9, v___x_5656_);
v___x_5668_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5669_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5667_);
lean_ctor_set(v___x_5670_, 1, v___x_5668_);
lean_ctor_set(v___x_5670_, 2, v___x_5638_);
lean_ctor_set(v___x_5670_, 3, v___x_5661_);
lean_ctor_set(v___x_5670_, 4, v___x_5669_);
v___x_5671_ = lean_st_mk_ref(v___x_5670_);
v___x_5672_ = l_Lean_Meta_addDefaultInstance(v_declName_5640_, v_a_5649_, v___x_5666_, v___x_5671_, v___y_5651_, v___y_5652_);
lean_dec_ref(v___x_5666_);
if (lean_obj_tag(v___x_5672_) == 0)
{
lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5681_; 
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5681_ == 0)
{
lean_object* v_unused_5682_; 
v_unused_5682_ = lean_ctor_get(v___x_5672_, 0);
lean_dec(v_unused_5682_);
v___x_5674_ = v___x_5672_;
v_isShared_5675_ = v_isSharedCheck_5681_;
goto v_resetjp_5673_;
}
else
{
lean_dec(v___x_5672_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5681_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5679_; 
v___x_5676_ = lean_st_ref_get(v___x_5671_);
lean_dec(v___x_5671_);
lean_dec(v___x_5676_);
v___x_5677_ = lean_box(0);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 0, v___x_5677_);
v___x_5679_ = v___x_5674_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v___x_5677_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
else
{
lean_dec(v___x_5671_);
return v___x_5672_;
}
}
}
else
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5693_; 
lean_dec(v_declName_5640_);
lean_dec(v___x_5639_);
lean_dec(v___x_5638_);
lean_dec(v___x_5637_);
v_a_5686_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5688_ = v___x_5648_;
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5648_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5689_ == 0)
{
v___x_5691_ = v___x_5688_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5686_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5694_, lean_object* v___x_5695_, lean_object* v___x_5696_, lean_object* v_declName_5697_, lean_object* v_stx_5698_, lean_object* v_kind_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
uint8_t v_kind_boxed_5703_; lean_object* v_res_5704_; 
v_kind_boxed_5703_ = lean_unbox(v_kind_5699_);
v_res_5704_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5694_, v___x_5695_, v___x_5696_, v_declName_5697_, v_stx_5698_, v_kind_boxed_5703_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v_stx_5698_);
return v_res_5704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5706_; lean_object* v___x_5707_; 
v___x_5706_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5707_ = l_Lean_stringToMessageData(v___x_5706_);
return v___x_5707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5710_ = l_Lean_stringToMessageData(v___x_5709_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5711_, lean_object* v_decl_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5716_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5717_ = l_Lean_MessageData_ofName(v___x_5711_);
v___x_5718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5718_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5720_, v___y_5713_, v___y_5714_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5722_, lean_object* v_decl_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v_res_5727_; 
v_res_5727_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5722_, v_decl_5723_, v___y_5724_, v___y_5725_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec(v_decl_5723_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5760_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5761_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5762_ = l_Lean_registerBuiltinAttribute(v___x_5761_);
if (lean_obj_tag(v___x_5762_) == 0)
{
lean_object* v___x_5763_; uint8_t v___x_5764_; lean_object* v___x_5765_; 
lean_dec_ref(v___x_5762_);
v___x_5763_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5764_ = 0;
v___x_5765_ = l_Lean_registerTraceClass(v___x_5763_, v___x_5764_, v___x_5760_);
return v___x_5765_;
}
else
{
return v___x_5762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5766_){
_start:
{
lean_object* v_res_5767_; 
v_res_5767_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5768_, lean_object* v_name_5769_, uint8_t v_kind_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v___x_5774_; 
v___x_5774_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5769_, v_kind_5770_, v___y_5771_, v___y_5772_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5775_, lean_object* v_name_5776_, lean_object* v_kind_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
uint8_t v_kind_boxed_5781_; lean_object* v_res_5782_; 
v_kind_boxed_5781_ = lean_unbox(v_kind_5777_);
v_res_5782_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5775_, v_name_5776_, v_kind_boxed_5781_, v___y_5778_, v___y_5779_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
return v_res_5782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5783_, lean_object* v_toPure_5784_, lean_object* v_____do__lift_5785_){
_start:
{
lean_object* v___x_5786_; lean_object* v_toEnvExtension_5787_; lean_object* v_asyncMode_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v_priorities_5791_; lean_object* v___x_5792_; 
v___x_5786_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5787_ = lean_ctor_get(v___x_5786_, 0);
v_asyncMode_5788_ = lean_ctor_get(v_toEnvExtension_5787_, 2);
v___x_5789_ = lean_box(0);
v___x_5790_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5783_, v___x_5786_, v_____do__lift_5785_, v_asyncMode_5788_, v___x_5789_);
v_priorities_5791_ = lean_ctor_get(v___x_5790_, 1);
lean_inc(v_priorities_5791_);
lean_dec(v___x_5790_);
v___x_5792_ = lean_apply_2(v_toPure_5784_, lean_box(0), v_priorities_5791_);
return v___x_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5793_, lean_object* v_inst_5794_){
_start:
{
lean_object* v_toApplicative_5795_; lean_object* v_toBind_5796_; lean_object* v_getEnv_5797_; lean_object* v_toPure_5798_; lean_object* v___x_5799_; lean_object* v___f_5800_; lean_object* v___x_5801_; 
v_toApplicative_5795_ = lean_ctor_get(v_inst_5793_, 0);
lean_inc_ref(v_toApplicative_5795_);
v_toBind_5796_ = lean_ctor_get(v_inst_5793_, 1);
lean_inc(v_toBind_5796_);
lean_dec_ref(v_inst_5793_);
v_getEnv_5797_ = lean_ctor_get(v_inst_5794_, 0);
lean_inc(v_getEnv_5797_);
lean_dec_ref(v_inst_5794_);
v_toPure_5798_ = lean_ctor_get(v_toApplicative_5795_, 1);
lean_inc(v_toPure_5798_);
lean_dec_ref(v_toApplicative_5795_);
v___x_5799_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5800_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5800_, 0, v___x_5799_);
lean_closure_set(v___f_5800_, 1, v_toPure_5798_);
v___x_5801_ = lean_apply_4(v_toBind_5796_, lean_box(0), lean_box(0), v_getEnv_5797_, v___f_5800_);
return v___x_5801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5802_, lean_object* v_inst_5803_, lean_object* v_inst_5804_){
_start:
{
lean_object* v___x_5805_; 
v___x_5805_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5803_, v_inst_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5806_, lean_object* v_className_5807_, lean_object* v_toPure_5808_, lean_object* v_____do__lift_5809_){
_start:
{
lean_object* v___x_5810_; lean_object* v_toEnvExtension_5811_; lean_object* v_asyncMode_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v_defaultInstances_5815_; lean_object* v___x_5816_; 
v___x_5810_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5811_ = lean_ctor_get(v___x_5810_, 0);
v_asyncMode_5812_ = lean_ctor_get(v_toEnvExtension_5811_, 2);
v___x_5813_ = lean_box(0);
v___x_5814_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5806_, v___x_5810_, v_____do__lift_5809_, v_asyncMode_5812_, v___x_5813_);
v_defaultInstances_5815_ = lean_ctor_get(v___x_5814_, 0);
lean_inc(v_defaultInstances_5815_);
lean_dec(v___x_5814_);
v___x_5816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5815_, v_className_5807_);
lean_dec(v_defaultInstances_5815_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5817_ = lean_box(0);
v___x_5818_ = lean_apply_2(v_toPure_5808_, lean_box(0), v___x_5817_);
return v___x_5818_;
}
else
{
lean_object* v_val_5819_; lean_object* v___x_5820_; 
v_val_5819_ = lean_ctor_get(v___x_5816_, 0);
lean_inc(v_val_5819_);
lean_dec_ref(v___x_5816_);
v___x_5820_ = lean_apply_2(v_toPure_5808_, lean_box(0), v_val_5819_);
return v___x_5820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5821_, lean_object* v_className_5822_, lean_object* v_toPure_5823_, lean_object* v_____do__lift_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5821_, v_className_5822_, v_toPure_5823_, v_____do__lift_5824_);
lean_dec(v_className_5822_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5826_, lean_object* v_inst_5827_, lean_object* v_className_5828_){
_start:
{
lean_object* v_toApplicative_5829_; lean_object* v_toBind_5830_; lean_object* v_getEnv_5831_; lean_object* v_toPure_5832_; lean_object* v___x_5833_; lean_object* v___f_5834_; lean_object* v___x_5835_; 
v_toApplicative_5829_ = lean_ctor_get(v_inst_5826_, 0);
lean_inc_ref(v_toApplicative_5829_);
v_toBind_5830_ = lean_ctor_get(v_inst_5826_, 1);
lean_inc(v_toBind_5830_);
lean_dec_ref(v_inst_5826_);
v_getEnv_5831_ = lean_ctor_get(v_inst_5827_, 0);
lean_inc(v_getEnv_5831_);
lean_dec_ref(v_inst_5827_);
v_toPure_5832_ = lean_ctor_get(v_toApplicative_5829_, 1);
lean_inc(v_toPure_5832_);
lean_dec_ref(v_toApplicative_5829_);
v___x_5833_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5834_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5834_, 0, v___x_5833_);
lean_closure_set(v___f_5834_, 1, v_className_5828_);
lean_closure_set(v___f_5834_, 2, v_toPure_5832_);
v___x_5835_ = lean_apply_4(v_toBind_5830_, lean_box(0), lean_box(0), v_getEnv_5831_, v___f_5834_);
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5836_, lean_object* v_inst_5837_, lean_object* v_inst_5838_, lean_object* v_className_5839_){
_start:
{
lean_object* v___x_5840_; 
v___x_5840_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5837_, v_inst_5838_, v_className_5839_);
return v___x_5840_;
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
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
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
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
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
