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
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "synthInstance"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkSynthOrder"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 153, 166, 25, 45, 140, 142, 203)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 121, 149, 143, 151, 161, 209, 111)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "check that instances do not introduce metavariable in non-out-params"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(210, 135, 61, 136, 69, 26, 61, 117)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 212, 166, 255, 222, 243, 240, 184)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instanceExtension"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 253, 187, 89, 234, 162, 232, 19)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
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
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Instances"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 69, 223, 114, 12, 235, 248, 125)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(245, 103, 148, 95, 163, 61, 86, 28)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(96, 213, 176, 90, 5, 29, 4, 245)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 119, 91, 79, 218, 216, 4, 30)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 34, 109, 117, 86, 219, 202, 202)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 31, 67, 74, 73, 155, 87, 189)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 214, 117, 3, 115, 221, 181, 118)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(189, 44, 126, 187, 224, 191, 65, 145)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "defaultInstanceExtension"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 56, 120, 160, 178, 206, 131, 123)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addDefaultInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
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
v___x_109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__0, &l_Lean_Meta_instInhabitedInstances_default___closed__0_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__2(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_box(0));
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_114_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__1, &l_Lean_Meta_instInhabitedInstances_default___closed__1_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__1);
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
lean_ctor_set(v___x_115_, 2, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__3, &l_Lean_Meta_instInhabitedInstances_default___closed__3_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__3);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_instInhabitedInstances_default;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_147_; 
v_ks_122_ = lean_ctor_get(v_x_118_, 0);
v_vs_123_ = lean_ctor_get(v_x_118_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_118_);
if (v_isSharedCheck_147_ == 0)
{
v___x_125_ = v_x_118_;
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_vs_123_);
lean_inc(v_ks_122_);
lean_dec(v_x_118_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_array_get_size(v_ks_122_);
v___x_128_ = lean_nat_dec_lt(v_x_119_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
lean_dec(v_x_119_);
v___x_129_ = lean_array_push(v_ks_122_, v_x_120_);
v___x_130_ = lean_array_push(v_vs_123_, v_x_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_130_);
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v_k_x27_134_; uint8_t v___x_135_; 
v_k_x27_134_ = lean_array_fget_borrowed(v_ks_122_, v_x_119_);
v___x_135_ = lean_name_eq(v_x_120_, v_k_x27_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_137_; 
if (v_isShared_126_ == 0)
{
v___x_137_ = v___x_125_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_ks_122_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_vs_123_);
v___x_137_ = v_reuseFailAlloc_141_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_x_119_, v___x_138_);
lean_dec(v_x_119_);
v_x_118_ = v___x_137_;
v_x_119_ = v___x_139_;
goto _start;
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = lean_array_fset(v_ks_122_, v_x_119_, v_x_120_);
v___x_143_ = lean_array_fset(v_vs_123_, v_x_119_, v_x_121_);
lean_dec(v_x_119_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_143_);
lean_ctor_set(v___x_125_, 0, v___x_142_);
v___x_145_ = v___x_125_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(lean_object* v_n_148_, lean_object* v_k_149_, lean_object* v_v_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_n_148_, v___x_151_, v_k_149_, v_v_150_);
return v___x_152_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_153_; uint64_t v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1723u);
v___x_154_ = lean_uint64_of_nat(v___x_153_);
return v___x_154_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; 
v___x_155_ = ((size_t)5ULL);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_shift_left(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; 
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0);
v___x_160_ = lean_usize_sub(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(lean_object* v_x_162_, size_t v_x_163_, size_t v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v_es_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v_j_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_es_167_ = lean_ctor_get(v_x_162_, 0);
v___x_168_ = ((size_t)5ULL);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_171_ = lean_usize_land(v_x_163_, v___x_170_);
v_j_172_ = lean_usize_to_nat(v___x_171_);
v___x_173_ = lean_array_get_size(v_es_167_);
v___x_174_ = lean_nat_dec_lt(v_j_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v_j_172_);
lean_dec(v_x_166_);
lean_dec(v_x_165_);
return v_x_162_;
}
else
{
lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_211_; 
lean_inc_ref(v_es_167_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_x_162_, 0);
lean_dec(v_unused_212_);
v___x_176_ = v_x_162_;
v_isShared_177_ = v_isSharedCheck_211_;
goto v_resetjp_175_;
}
else
{
lean_dec(v_x_162_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_211_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_v_178_; lean_object* v___x_179_; lean_object* v_xs_x27_180_; lean_object* v___y_182_; 
v_v_178_ = lean_array_fget(v_es_167_, v_j_172_);
v___x_179_ = lean_box(0);
v_xs_x27_180_ = lean_array_fset(v_es_167_, v_j_172_, v___x_179_);
switch(lean_obj_tag(v_v_178_))
{
case 0:
{
lean_object* v_key_187_; lean_object* v_val_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_198_; 
v_key_187_ = lean_ctor_get(v_v_178_, 0);
v_val_188_ = lean_ctor_get(v_v_178_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_v_178_);
if (v_isSharedCheck_198_ == 0)
{
v___x_190_ = v_v_178_;
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_val_188_);
lean_inc(v_key_187_);
lean_dec(v_v_178_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
uint8_t v___x_192_; 
v___x_192_ = lean_name_eq(v_x_165_, v_key_187_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_del_object(v___x_190_);
v___x_193_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_187_, v_val_188_, v_x_165_, v_x_166_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
v___y_182_ = v___x_194_;
goto v___jp_181_;
}
else
{
lean_object* v___x_196_; 
lean_dec(v_val_188_);
lean_dec(v_key_187_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_x_166_);
lean_ctor_set(v___x_190_, 0, v_x_165_);
v___x_196_ = v___x_190_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_x_165_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_x_166_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
}
}
}
case 1:
{
lean_object* v_node_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_209_; 
v_node_199_ = lean_ctor_get(v_v_178_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_v_178_);
if (v_isSharedCheck_209_ == 0)
{
v___x_201_ = v_v_178_;
v_isShared_202_ = v_isSharedCheck_209_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_node_199_);
lean_dec(v_v_178_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_209_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_203_ = lean_usize_shift_right(v_x_163_, v___x_168_);
v___x_204_ = lean_usize_add(v_x_164_, v___x_169_);
v___x_205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_node_199_, v___x_203_, v___x_204_, v_x_165_, v_x_166_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_205_);
v___x_207_ = v___x_201_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v___y_182_ = v___x_207_;
goto v___jp_181_;
}
}
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_x_165_);
lean_ctor_set(v___x_210_, 1, v_x_166_);
v___y_182_ = v___x_210_;
goto v___jp_181_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_array_fset(v_xs_x27_180_, v_j_172_, v___y_182_);
lean_dec(v_j_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_183_);
v___x_185_ = v___x_176_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
else
{
lean_object* v_ks_213_; lean_object* v_vs_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_234_; 
v_ks_213_ = lean_ctor_get(v_x_162_, 0);
v_vs_214_ = lean_ctor_get(v_x_162_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_234_ == 0)
{
v___x_216_ = v_x_162_;
v_isShared_217_ = v_isSharedCheck_234_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_vs_214_);
lean_inc(v_ks_213_);
lean_dec(v_x_162_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_234_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_ks_213_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_vs_214_);
v___x_219_ = v_reuseFailAlloc_233_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v_newNode_220_; uint8_t v___y_222_; size_t v___x_228_; uint8_t v___x_229_; 
v_newNode_220_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v___x_219_, v_x_165_, v_x_166_);
v___x_228_ = ((size_t)7ULL);
v___x_229_ = lean_usize_dec_le(v___x_228_, v_x_164_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_220_);
v___x_231_ = lean_unsigned_to_nat(4u);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___y_222_ = v___x_232_;
goto v___jp_221_;
}
else
{
v___y_222_ = v___x_229_;
goto v___jp_221_;
}
v___jp_221_:
{
if (v___y_222_ == 0)
{
lean_object* v_ks_223_; lean_object* v_vs_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_ks_223_ = lean_ctor_get(v_newNode_220_, 0);
lean_inc_ref(v_ks_223_);
v_vs_224_ = lean_ctor_get(v_newNode_220_, 1);
lean_inc_ref(v_vs_224_);
lean_dec_ref(v_newNode_220_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_x_164_, v_ks_223_, v_vs_224_, v___x_225_, v___x_226_);
lean_dec_ref(v_vs_224_);
lean_dec_ref(v_ks_223_);
return v___x_227_;
}
else
{
return v_newNode_220_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(size_t v_depth_235_, lean_object* v_keys_236_, lean_object* v_vals_237_, lean_object* v_i_238_, lean_object* v_entries_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_array_get_size(v_keys_236_);
v___x_241_ = lean_nat_dec_lt(v_i_238_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v_i_238_);
return v_entries_239_;
}
else
{
lean_object* v_k_242_; lean_object* v_v_243_; uint64_t v___y_245_; 
v_k_242_ = lean_array_fget_borrowed(v_keys_236_, v_i_238_);
v_v_243_ = lean_array_fget_borrowed(v_vals_237_, v_i_238_);
if (lean_obj_tag(v_k_242_) == 0)
{
uint64_t v___x_256_; 
v___x_256_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_245_ = v___x_256_;
goto v___jp_244_;
}
else
{
uint64_t v_hash_257_; 
v_hash_257_ = lean_ctor_get_uint64(v_k_242_, sizeof(void*)*2);
v___y_245_ = v_hash_257_;
goto v___jp_244_;
}
v___jp_244_:
{
size_t v_h_246_; size_t v___x_247_; lean_object* v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v_h_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_h_246_ = lean_uint64_to_usize(v___y_245_);
v___x_247_ = ((size_t)5ULL);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v_depth_235_, v___x_249_);
v___x_251_ = lean_usize_mul(v___x_247_, v___x_250_);
v_h_252_ = lean_usize_shift_right(v_h_246_, v___x_251_);
v___x_253_ = lean_nat_add(v_i_238_, v___x_248_);
lean_dec(v_i_238_);
lean_inc(v_v_243_);
lean_inc(v_k_242_);
v___x_254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_entries_239_, v_h_252_, v_depth_235_, v_k_242_, v_v_243_);
v_i_238_ = v___x_253_;
v_entries_239_ = v___x_254_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_258_, lean_object* v_keys_259_, lean_object* v_vals_260_, lean_object* v_i_261_, lean_object* v_entries_262_){
_start:
{
size_t v_depth_boxed_263_; lean_object* v_res_264_; 
v_depth_boxed_263_ = lean_unbox_usize(v_depth_258_);
lean_dec(v_depth_258_);
v_res_264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_boxed_263_, v_keys_259_, v_vals_260_, v_i_261_, v_entries_262_);
lean_dec_ref(v_vals_260_);
lean_dec_ref(v_keys_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___boxed(lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
size_t v_x_2078__boxed_270_; size_t v_x_2079__boxed_271_; lean_object* v_res_272_; 
v_x_2078__boxed_270_ = lean_unbox_usize(v_x_266_);
lean_dec(v_x_266_);
v_x_2079__boxed_271_ = lean_unbox_usize(v_x_267_);
lean_dec(v_x_267_);
v_res_272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_265_, v_x_2078__boxed_270_, v_x_2079__boxed_271_, v_x_268_, v_x_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint64_t v___y_277_; 
if (lean_obj_tag(v_x_274_) == 0)
{
uint64_t v___x_281_; 
v___x_281_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_277_ = v___x_281_;
goto v___jp_276_;
}
else
{
uint64_t v_hash_282_; 
v_hash_282_ = lean_ctor_get_uint64(v_x_274_, sizeof(void*)*2);
v___y_277_ = v_hash_282_;
goto v___jp_276_;
}
v___jp_276_:
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_uint64_to_usize(v___y_277_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_273_, v___x_278_, v___x_279_, v_x_274_, v_x_275_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(lean_object* v_vs_283_, lean_object* v_v_284_, lean_object* v_i_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_vs_283_);
v___x_287_ = lean_nat_dec_lt(v_i_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_i_285_);
v___x_288_ = lean_array_push(v_vs_283_, v_v_284_);
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_290_; lean_object* v_val_291_; uint8_t v___x_292_; 
v_val_289_ = lean_ctor_get(v_v_284_, 1);
v___x_290_ = lean_array_fget_borrowed(v_vs_283_, v_i_285_);
v_val_291_ = lean_ctor_get(v___x_290_, 1);
v___x_292_ = lean_expr_eqv(v_val_289_, v_val_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_i_285_, v___x_293_);
lean_dec(v_i_285_);
v_i_285_ = v___x_294_;
goto _start;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_array_fset(v_vs_283_, v_i_285_, v_v_284_);
lean_dec(v_i_285_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(lean_object* v_vs_297_, lean_object* v_v_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(v_vs_297_, v_v_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_301_, lean_object* v_b_302_){
_start:
{
lean_object* v_fst_303_; lean_object* v_fst_304_; uint8_t v___x_305_; 
v_fst_303_ = lean_ctor_get(v_a_301_, 0);
v_fst_304_ = lean_ctor_get(v_b_302_, 0);
v___x_305_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_303_, v_fst_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_a_306_, v_b_307_);
lean_dec_ref(v_b_307_);
lean_dec_ref(v_a_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_310_, lean_object* v_keys_311_, lean_object* v_v_312_, lean_object* v_k_313_, lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_c_317_; lean_object* v___x_318_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_x_310_, v___x_315_);
v_c_317_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_311_, v_v_312_, v___x_316_);
lean_dec(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_k_313_);
lean_ctor_set(v___x_318_, 1, v_c_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_319_, lean_object* v_keys_320_, lean_object* v_v_321_, lean_object* v_k_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_319_, v_keys_320_, v_v_321_, v_k_322_, v_x_323_);
lean_dec_ref(v_keys_320_);
lean_dec(v_x_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(lean_object* v_x_329_, lean_object* v_keys_330_, lean_object* v_v_331_, lean_object* v_k_332_, lean_object* v_as_333_, lean_object* v_k_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_mid_339_; lean_object* v_midVal_340_; uint8_t v___x_341_; 
v___x_337_ = lean_nat_add(v_x_335_, v_x_336_);
v___x_338_ = lean_unsigned_to_nat(1u);
v_mid_339_ = lean_nat_shiftr(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
v_midVal_340_ = lean_array_fget(v_as_333_, v_mid_339_);
v___x_341_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_midVal_340_, v_k_334_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
lean_dec(v_x_336_);
v___x_342_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_334_, v_midVal_340_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
lean_dec(v_x_335_);
v___x_343_ = lean_array_get_size(v_as_333_);
v___x_344_ = lean_nat_dec_lt(v_mid_339_, v___x_343_);
if (v___x_344_ == 0)
{
lean_dec(v_midVal_340_);
lean_dec(v_mid_339_);
lean_dec(v_k_332_);
lean_dec_ref(v_v_331_);
return v_as_333_;
}
else
{
lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_357_; 
v_snd_345_ = lean_ctor_get(v_midVal_340_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_midVal_340_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_midVal_340_, 0);
lean_dec(v_unused_358_);
v___x_347_ = v_midVal_340_;
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_dec(v_midVal_340_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v_xs_x27_350_; lean_object* v___x_351_; lean_object* v_c_352_; lean_object* v___x_354_; 
v___x_349_ = lean_box(0);
v_xs_x27_350_ = lean_array_fset(v_as_333_, v_mid_339_, v___x_349_);
v___x_351_ = lean_nat_add(v_x_329_, v___x_338_);
v_c_352_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_330_, v_v_331_, v___x_351_, v_snd_345_);
lean_dec(v___x_351_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_c_352_);
lean_ctor_set(v___x_347_, 0, v_k_332_);
v___x_354_ = v___x_347_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_k_332_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_c_352_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = lean_array_fset(v_xs_x27_350_, v_mid_339_, v___x_354_);
lean_dec(v_mid_339_);
return v___x_355_;
}
}
}
}
else
{
lean_dec(v_midVal_340_);
v_x_336_ = v_mid_339_;
goto _start;
}
}
else
{
uint8_t v___x_360_; 
lean_dec(v_midVal_340_);
v___x_360_ = lean_nat_dec_eq(v_mid_339_, v_x_335_);
if (v___x_360_ == 0)
{
lean_dec(v_x_335_);
v_x_335_ = v_mid_339_;
goto _start;
}
else
{
lean_object* v___x_362_; lean_object* v_c_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_j_366_; lean_object* v_as_367_; lean_object* v___x_368_; 
lean_dec(v_mid_339_);
lean_dec(v_x_336_);
v___x_362_ = lean_nat_add(v_x_329_, v___x_338_);
v_c_363_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_330_, v_v_331_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_k_332_);
lean_ctor_set(v___x_364_, 1, v_c_363_);
v___x_365_ = lean_nat_add(v_x_335_, v___x_338_);
lean_dec(v_x_335_);
v_j_366_ = lean_array_get_size(v_as_333_);
v_as_367_ = lean_array_push(v_as_333_, v___x_364_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_365_, v_as_367_, v_j_366_);
lean_dec(v___x_365_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(lean_object* v_x_369_, lean_object* v_keys_370_, lean_object* v_v_371_, lean_object* v_k_372_, lean_object* v_as_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_array_get_size(v_as_373_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_fget_borrowed(v_as_373_, v___x_376_);
v___x_379_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_374_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_378_, v_k_374_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_lt(v___x_376_, v___x_375_);
if (v___x_381_ == 0)
{
lean_dec(v_k_372_);
lean_dec_ref(v_v_371_);
return v_as_373_;
}
else
{
lean_object* v___x_382_; lean_object* v_xs_x27_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc(v___x_378_);
v___x_382_ = lean_box(0);
v_xs_x27_383_ = lean_array_fset(v_as_373_, v___x_376_, v___x_382_);
v___x_384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v___x_378_);
v___x_385_ = lean_array_fset(v_xs_x27_383_, v___x_376_, v___x_384_);
return v___x_385_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_sub(v___x_375_, v___x_386_);
v___x_388_ = lean_array_fget_borrowed(v_as_373_, v___x_387_);
v___x_389_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_388_, v_k_374_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; 
v___x_390_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_374_, v___x_388_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_lt(v___x_387_, v___x_375_);
if (v___x_391_ == 0)
{
lean_dec(v___x_387_);
lean_dec(v_k_372_);
lean_dec_ref(v_v_371_);
return v_as_373_;
}
else
{
lean_object* v___x_392_; lean_object* v_xs_x27_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc(v___x_388_);
v___x_392_ = lean_box(0);
v_xs_x27_393_ = lean_array_fset(v_as_373_, v___x_387_, v___x_392_);
v___x_394_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v___x_388_);
v___x_395_ = lean_array_fset(v_xs_x27_393_, v___x_387_, v___x_394_);
lean_dec(v___x_387_);
return v___x_395_;
}
}
else
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v_as_373_, v_k_374_, v___x_376_, v___x_387_);
return v___x_396_;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v___x_387_);
v___x_397_ = lean_box(0);
v___x_398_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v___x_397_);
v___x_399_ = lean_array_push(v_as_373_, v___x_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_as_402_; lean_object* v___x_403_; 
v___x_400_ = lean_box(0);
v___x_401_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v___x_400_);
v_as_402_ = lean_array_push(v_as_373_, v___x_401_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_376_, v_as_402_, v___x_375_);
return v___x_403_;
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
v___x_405_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_369_, v_keys_370_, v_v_371_, v_k_372_, v___x_404_);
v___x_406_ = lean_array_push(v_as_373_, v___x_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_keys_407_, lean_object* v_v_408_, lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_vs_411_; lean_object* v_children_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_429_; 
v_vs_411_ = lean_ctor_get(v_x_410_, 0);
v_children_412_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_429_ == 0)
{
v___x_414_ = v_x_410_;
v_isShared_415_ = v_isSharedCheck_429_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_children_412_);
lean_inc(v_vs_411_);
lean_dec(v_x_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_429_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_array_get_size(v_keys_407_);
v___x_417_ = lean_nat_dec_lt(v_x_409_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(v_vs_411_, v_v_408_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_418_);
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_children_412_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v_k_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_c_425_; lean_object* v___x_427_; 
v_k_422_ = lean_array_fget_borrowed(v_keys_407_, v_x_409_);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1));
lean_inc_n(v_k_422_, 2);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_k_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v_c_425_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_409_, v_keys_407_, v_v_408_, v_k_422_, v_children_412_, v___x_424_);
lean_dec_ref(v___x_424_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v_c_425_);
v___x_427_ = v___x_414_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_vs_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_c_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_430_, lean_object* v_keys_431_, lean_object* v_v_432_, lean_object* v_k_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v_snd_435_ = lean_ctor_get(v_x_434_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_x_434_, 0);
lean_dec(v_unused_446_);
v___x_437_ = v_x_434_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_dec(v_x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_c_441_; lean_object* v___x_443_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_x_430_, v___x_439_);
v_c_441_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_431_, v_v_432_, v___x_440_, v_snd_435_);
lean_dec(v___x_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_c_441_);
lean_ctor_set(v___x_437_, 0, v_k_433_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_k_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_c_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_447_, lean_object* v_keys_448_, lean_object* v_v_449_, lean_object* v_k_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_447_, v_keys_448_, v_v_449_, v_k_450_, v_x_451_);
lean_dec_ref(v_keys_448_);
lean_dec(v_x_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___boxed(lean_object* v_keys_453_, lean_object* v_v_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_453_, v_v_454_, v_x_455_, v_x_456_);
lean_dec(v_x_455_);
lean_dec_ref(v_keys_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_x_458_, lean_object* v_keys_459_, lean_object* v_v_460_, lean_object* v_k_461_, lean_object* v_as_462_, lean_object* v_k_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_458_, v_keys_459_, v_v_460_, v_k_461_, v_as_462_, v_k_463_, v_x_464_, v_x_465_);
lean_dec_ref(v_k_463_);
lean_dec_ref(v_keys_459_);
lean_dec(v_x_458_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___boxed(lean_object* v_x_467_, lean_object* v_keys_468_, lean_object* v_v_469_, lean_object* v_k_470_, lean_object* v_as_471_, lean_object* v_k_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_467_, v_keys_468_, v_v_469_, v_k_470_, v_as_471_, v_k_472_);
lean_dec_ref(v_k_472_);
lean_dec_ref(v_keys_468_);
lean_dec(v_x_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_i_476_, lean_object* v_k_477_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_array_get_size(v_keys_474_);
v___x_479_ = lean_nat_dec_lt(v_i_476_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec(v_i_476_);
v___x_480_ = lean_box(0);
return v___x_480_;
}
else
{
lean_object* v_k_x27_481_; uint8_t v___x_482_; 
v_k_x27_481_ = lean_array_fget_borrowed(v_keys_474_, v_i_476_);
v___x_482_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_477_, v_k_x27_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_i_476_, v___x_483_);
lean_dec(v_i_476_);
v_i_476_ = v___x_484_;
goto _start;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_array_fget_borrowed(v_vals_475_, v_i_476_);
lean_dec(v_i_476_);
lean_inc(v___x_486_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_keys_488_, lean_object* v_vals_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_488_, v_vals_489_, v_i_490_, v_k_491_);
lean_dec(v_k_491_);
lean_dec_ref(v_vals_489_);
lean_dec_ref(v_keys_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_493_, size_t v_x_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_es_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_517_; 
v_es_496_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_517_ == 0)
{
v___x_498_ = v_x_493_;
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_es_496_);
lean_dec(v_x_493_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v_j_504_; lean_object* v___x_505_; 
v___x_500_ = lean_box(2);
v___x_501_ = ((size_t)5ULL);
v___x_502_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_503_ = lean_usize_land(v_x_494_, v___x_502_);
v_j_504_ = lean_usize_to_nat(v___x_503_);
v___x_505_ = lean_array_get(v___x_500_, v_es_496_, v_j_504_);
lean_dec(v_j_504_);
lean_dec_ref(v_es_496_);
switch(lean_obj_tag(v___x_505_))
{
case 0:
{
lean_object* v_key_506_; lean_object* v_val_507_; uint8_t v___x_508_; 
v_key_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_key_506_);
v_val_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_val_507_);
lean_dec_ref(v___x_505_);
v___x_508_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_495_, v_key_506_);
lean_dec(v_key_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec(v_val_507_);
lean_del_object(v___x_498_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v___x_511_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
lean_ctor_set(v___x_498_, 0, v_val_507_);
v___x_511_ = v___x_498_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_val_507_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
case 1:
{
lean_object* v_node_513_; size_t v___x_514_; 
lean_del_object(v___x_498_);
v_node_513_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_node_513_);
lean_dec_ref(v___x_505_);
v___x_514_ = lean_usize_shift_right(v_x_494_, v___x_501_);
v_x_493_ = v_node_513_;
v_x_494_ = v___x_514_;
goto _start;
}
default: 
{
lean_object* v___x_516_; 
lean_del_object(v___x_498_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
}
}
}
else
{
lean_object* v_ks_518_; lean_object* v_vs_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_ks_518_ = lean_ctor_get(v_x_493_, 0);
lean_inc_ref(v_ks_518_);
v_vs_519_ = lean_ctor_get(v_x_493_, 1);
lean_inc_ref(v_vs_519_);
lean_dec_ref(v_x_493_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_518_, v_vs_519_, v___x_520_, v_x_495_);
lean_dec_ref(v_vs_519_);
lean_dec_ref(v_ks_518_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
size_t v_x_2529__boxed_525_; lean_object* v_res_526_; 
v_x_2529__boxed_525_ = lean_unbox_usize(v_x_523_);
lean_dec(v_x_523_);
v_res_526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_522_, v_x_2529__boxed_525_, v_x_524_);
lean_dec(v_x_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
uint64_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_528_);
v___x_530_ = lean_uint64_to_usize(v___x_529_);
v___x_531_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_527_, v___x_530_, v_x_528_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_532_, v_x_533_);
lean_dec(v_x_533_);
return v_res_534_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(lean_object* v_msg_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0);
v___x_538_ = lean_panic_fn_borrowed(v___x_537_, v_msg_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_ks_543_; lean_object* v_vs_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_568_; 
v_ks_543_ = lean_ctor_get(v_x_539_, 0);
v_vs_544_ = lean_ctor_get(v_x_539_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_568_ == 0)
{
v___x_546_ = v_x_539_;
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_vs_544_);
lean_inc(v_ks_543_);
lean_dec(v_x_539_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_array_get_size(v_ks_543_);
v___x_549_ = lean_nat_dec_lt(v_x_540_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_x_540_);
v___x_550_ = lean_array_push(v_ks_543_, v_x_541_);
v___x_551_ = lean_array_push(v_vs_544_, v_x_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_551_);
lean_ctor_set(v___x_546_, 0, v___x_550_);
v___x_553_ = v___x_546_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v_k_x27_555_; uint8_t v___x_556_; 
v_k_x27_555_ = lean_array_fget_borrowed(v_ks_543_, v_x_540_);
v___x_556_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_541_, v_k_x27_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_558_; 
if (v_isShared_547_ == 0)
{
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_ks_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_vs_544_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_x_540_, v___x_559_);
lean_dec(v_x_540_);
v_x_539_ = v___x_558_;
v_x_540_ = v___x_560_;
goto _start;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_563_ = lean_array_fset(v_ks_543_, v_x_540_, v_x_541_);
v___x_564_ = lean_array_fset(v_vs_544_, v_x_540_, v_x_542_);
lean_dec(v_x_540_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_564_);
lean_ctor_set(v___x_546_, 0, v___x_563_);
v___x_566_ = v___x_546_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_n_569_, lean_object* v_k_570_, lean_object* v_v_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_n_569_, v___x_572_, v_k_570_, v_v_571_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_x_575_, size_t v_x_576_, size_t v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v_es_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; lean_object* v_j_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_es_580_ = lean_ctor_get(v_x_575_, 0);
v___x_581_ = ((size_t)5ULL);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_584_ = lean_usize_land(v_x_576_, v___x_583_);
v_j_585_ = lean_usize_to_nat(v___x_584_);
v___x_586_ = lean_array_get_size(v_es_580_);
v___x_587_ = lean_nat_dec_lt(v_j_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v_j_585_);
lean_dec(v_x_579_);
lean_dec(v_x_578_);
return v_x_575_;
}
else
{
lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_624_; 
lean_inc_ref(v_es_580_);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v_x_575_, 0);
lean_dec(v_unused_625_);
v___x_589_ = v_x_575_;
v_isShared_590_ = v_isSharedCheck_624_;
goto v_resetjp_588_;
}
else
{
lean_dec(v_x_575_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_624_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_v_591_; lean_object* v___x_592_; lean_object* v_xs_x27_593_; lean_object* v___y_595_; 
v_v_591_ = lean_array_fget(v_es_580_, v_j_585_);
v___x_592_ = lean_box(0);
v_xs_x27_593_ = lean_array_fset(v_es_580_, v_j_585_, v___x_592_);
switch(lean_obj_tag(v_v_591_))
{
case 0:
{
lean_object* v_key_600_; lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_key_600_ = lean_ctor_get(v_v_591_, 0);
v_val_601_ = lean_ctor_get(v_v_591_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_v_591_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_v_591_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_inc(v_key_600_);
lean_dec(v_v_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
uint8_t v___x_605_; 
v___x_605_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_578_, v_key_600_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_del_object(v___x_603_);
v___x_606_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_600_, v_val_601_, v_x_578_, v_x_579_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
v___y_595_ = v___x_607_;
goto v___jp_594_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_val_601_);
lean_dec(v_key_600_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_x_579_);
lean_ctor_set(v___x_603_, 0, v_x_578_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_x_578_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_x_579_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v___y_595_ = v___x_609_;
goto v___jp_594_;
}
}
}
}
case 1:
{
lean_object* v_node_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
v_node_612_ = lean_ctor_get(v_v_591_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_v_591_);
if (v_isSharedCheck_622_ == 0)
{
v___x_614_ = v_v_591_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_node_612_);
lean_dec(v_v_591_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_616_ = lean_usize_shift_right(v_x_576_, v___x_581_);
v___x_617_ = lean_usize_add(v_x_577_, v___x_582_);
v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_node_612_, v___x_616_, v___x_617_, v_x_578_, v_x_579_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_618_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v___y_595_ = v___x_620_;
goto v___jp_594_;
}
}
}
default: 
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_x_578_);
lean_ctor_set(v___x_623_, 1, v_x_579_);
v___y_595_ = v___x_623_;
goto v___jp_594_;
}
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_array_fset(v_xs_x27_593_, v_j_585_, v___y_595_);
lean_dec(v_j_585_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_596_);
v___x_598_ = v___x_589_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_ks_626_; lean_object* v_vs_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_647_; 
v_ks_626_ = lean_ctor_get(v_x_575_, 0);
v_vs_627_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_647_ == 0)
{
v___x_629_ = v_x_575_;
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_vs_627_);
lean_inc(v_ks_626_);
lean_dec(v_x_575_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_ks_626_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_vs_627_);
v___x_632_ = v_reuseFailAlloc_646_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v_newNode_633_; uint8_t v___y_635_; size_t v___x_641_; uint8_t v___x_642_; 
v_newNode_633_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v___x_632_, v_x_578_, v_x_579_);
v___x_641_ = ((size_t)7ULL);
v___x_642_ = lean_usize_dec_le(v___x_641_, v_x_577_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_633_);
v___x_644_ = lean_unsigned_to_nat(4u);
v___x_645_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
lean_dec(v___x_643_);
v___y_635_ = v___x_645_;
goto v___jp_634_;
}
else
{
v___y_635_ = v___x_642_;
goto v___jp_634_;
}
v___jp_634_:
{
if (v___y_635_ == 0)
{
lean_object* v_ks_636_; lean_object* v_vs_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_ks_636_ = lean_ctor_get(v_newNode_633_, 0);
lean_inc_ref(v_ks_636_);
v_vs_637_ = lean_ctor_get(v_newNode_633_, 1);
lean_inc_ref(v_vs_637_);
lean_dec_ref(v_newNode_633_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_x_577_, v_ks_636_, v_vs_637_, v___x_638_, v___x_639_);
lean_dec_ref(v_vs_637_);
lean_dec_ref(v_ks_636_);
return v___x_640_;
}
else
{
return v_newNode_633_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(size_t v_depth_648_, lean_object* v_keys_649_, lean_object* v_vals_650_, lean_object* v_i_651_, lean_object* v_entries_652_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_array_get_size(v_keys_649_);
v___x_654_ = lean_nat_dec_lt(v_i_651_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v_i_651_);
return v_entries_652_;
}
else
{
lean_object* v_k_655_; lean_object* v_v_656_; uint64_t v___x_657_; size_t v_h_658_; size_t v___x_659_; lean_object* v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v_h_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_k_655_ = lean_array_fget_borrowed(v_keys_649_, v_i_651_);
v_v_656_ = lean_array_fget_borrowed(v_vals_650_, v_i_651_);
v___x_657_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_655_);
v_h_658_ = lean_uint64_to_usize(v___x_657_);
v___x_659_ = ((size_t)5ULL);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_sub(v_depth_648_, v___x_661_);
v___x_663_ = lean_usize_mul(v___x_659_, v___x_662_);
v_h_664_ = lean_usize_shift_right(v_h_658_, v___x_663_);
v___x_665_ = lean_nat_add(v_i_651_, v___x_660_);
lean_dec(v_i_651_);
lean_inc(v_v_656_);
lean_inc(v_k_655_);
v___x_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_entries_652_, v_h_664_, v_depth_648_, v_k_655_, v_v_656_);
v_i_651_ = v___x_665_;
v_entries_652_ = v___x_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_668_, lean_object* v_keys_669_, lean_object* v_vals_670_, lean_object* v_i_671_, lean_object* v_entries_672_){
_start:
{
size_t v_depth_boxed_673_; lean_object* v_res_674_; 
v_depth_boxed_673_ = lean_unbox_usize(v_depth_668_);
lean_dec(v_depth_668_);
v_res_674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_boxed_673_, v_keys_669_, v_vals_670_, v_i_671_, v_entries_672_);
lean_dec_ref(v_vals_670_);
lean_dec_ref(v_keys_669_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_2691__boxed_680_; size_t v_x_2692__boxed_681_; lean_object* v_res_682_; 
v_x_2691__boxed_680_ = lean_unbox_usize(v_x_676_);
lean_dec(v_x_676_);
v_x_2692__boxed_681_ = lean_unbox_usize(v_x_677_);
lean_dec(v_x_677_);
v_res_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_675_, v_x_2691__boxed_680_, v_x_2692__boxed_681_, v_x_678_, v_x_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_686_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_684_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_683_, v___x_687_, v___x_688_, v_x_684_, v_x_685_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_694_ = lean_unsigned_to_nat(23u);
v___x_695_ = lean_unsigned_to_nat(166u);
v___x_696_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_697_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_698_ = l_mkPanicMessageWithDecl(v___x_697_, v___x_696_, v___x_695_, v___x_694_, v___x_693_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_699_, lean_object* v_keys_700_, lean_object* v_v_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_array_get_size(v_keys_700_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v_k_706_; lean_object* v___x_707_; 
v___x_705_ = lean_box(0);
v_k_706_ = lean_array_get_borrowed(v___x_705_, v_keys_700_, v___x_703_);
lean_inc_ref(v_d_699_);
v___x_707_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_d_699_, v_k_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; lean_object* v_c_709_; lean_object* v___x_710_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v_c_709_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_700_, v_v_701_, v___x_708_);
lean_inc(v_k_706_);
v___x_710_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_699_, v_k_706_, v_c_709_);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_712_; lean_object* v_c_713_; lean_object* v___x_714_; 
v_val_711_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v___x_707_);
v___x_712_ = lean_unsigned_to_nat(1u);
v_c_713_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_700_, v_v_701_, v___x_712_, v_val_711_);
lean_inc(v_k_706_);
v___x_714_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_699_, v_k_706_, v_c_713_);
return v___x_714_;
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v_v_701_);
lean_dec_ref(v_d_699_);
v___x_715_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_716_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(v___x_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_717_, lean_object* v_keys_718_, lean_object* v_v_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_717_, v_keys_718_, v_v_719_);
lean_dec_ref(v_keys_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(lean_object* v_xs_721_, lean_object* v_v_722_, lean_object* v_i_723_){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_xs_721_);
v___x_725_ = lean_nat_dec_lt(v_i_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec(v_i_723_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_fget_borrowed(v_xs_721_, v_i_723_);
v___x_728_ = lean_name_eq(v___x_727_, v_v_722_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_i_723_, v___x_729_);
lean_dec(v_i_723_);
v_i_723_ = v___x_730_;
goto _start;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_i_723_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21___boxed(lean_object* v_xs_733_, lean_object* v_v_734_, lean_object* v_i_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_733_, v_v_734_, v_i_735_);
lean_dec(v_v_734_);
lean_dec_ref(v_xs_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(lean_object* v_xs_737_, lean_object* v_v_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_737_, v_v_738_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14___boxed(lean_object* v_xs_741_, lean_object* v_v_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_xs_741_, v_v_742_);
lean_dec(v_v_742_);
lean_dec_ref(v_xs_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(lean_object* v_x_744_, size_t v_x_745_, lean_object* v_x_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_es_747_; lean_object* v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v_j_752_; lean_object* v_entry_753_; 
v_es_747_ = lean_ctor_get(v_x_744_, 0);
v___x_748_ = lean_box(2);
v___x_749_ = ((size_t)5ULL);
v___x_750_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_751_ = lean_usize_land(v_x_745_, v___x_750_);
v_j_752_ = lean_usize_to_nat(v___x_751_);
v_entry_753_ = lean_array_get(v___x_748_, v_es_747_, v_j_752_);
switch(lean_obj_tag(v_entry_753_))
{
case 0:
{
lean_object* v_key_754_; uint8_t v___x_755_; 
v_key_754_ = lean_ctor_get(v_entry_753_, 0);
lean_inc(v_key_754_);
lean_dec_ref(v_entry_753_);
v___x_755_ = lean_name_eq(v_x_746_, v_key_754_);
lean_dec(v_key_754_);
if (v___x_755_ == 0)
{
lean_dec(v_j_752_);
return v_x_744_;
}
else
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
lean_inc_ref(v_es_747_);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_x_744_, 0);
lean_dec(v_unused_764_);
v___x_757_ = v_x_744_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_x_744_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_array_set(v_es_747_, v_j_752_, v___x_748_);
lean_dec(v_j_752_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
case 1:
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_798_; 
lean_inc_ref(v_es_747_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_x_744_, 0);
lean_dec(v_unused_799_);
v___x_766_ = v_x_744_;
v_isShared_767_ = v_isSharedCheck_798_;
goto v_resetjp_765_;
}
else
{
lean_dec(v_x_744_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_798_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_node_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_797_; 
v_node_768_ = lean_ctor_get(v_entry_753_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_entry_753_);
if (v_isSharedCheck_797_ == 0)
{
v___x_770_ = v_entry_753_;
v_isShared_771_ = v_isSharedCheck_797_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_node_768_);
lean_dec(v_entry_753_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_797_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_entries_772_; size_t v___x_773_; lean_object* v_newNode_774_; lean_object* v___x_775_; 
v_entries_772_ = lean_array_set(v_es_747_, v_j_752_, v___x_748_);
v___x_773_ = lean_usize_shift_right(v_x_745_, v___x_749_);
v_newNode_774_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_node_768_, v___x_773_, v_x_746_);
lean_inc_ref(v_newNode_774_);
v___x_775_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_777_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_newNode_774_);
v___x_777_ = v___x_770_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_newNode_774_);
v___x_777_ = v_reuseFailAlloc_782_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_array_set(v_entries_772_, v_j_752_, v___x_777_);
lean_dec(v_j_752_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_778_);
v___x_780_ = v___x_766_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_val_783_; lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v_newNode_774_);
lean_del_object(v___x_770_);
v_val_783_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_783_);
lean_dec_ref(v___x_775_);
v_fst_784_ = lean_ctor_get(v_val_783_, 0);
v_snd_785_ = lean_ctor_get(v_val_783_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_val_783_);
if (v_isSharedCheck_796_ == 0)
{
v___x_787_ = v_val_783_;
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snd_785_);
lean_inc(v_fst_784_);
lean_dec(v_val_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_785_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_array_set(v_entries_772_, v_j_752_, v___x_790_);
lean_dec(v_j_752_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_791_);
v___x_793_ = v___x_766_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_752_);
return v_x_744_;
}
}
}
else
{
lean_object* v_ks_800_; lean_object* v_vs_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_815_; 
v_ks_800_ = lean_ctor_get(v_x_744_, 0);
v_vs_801_ = lean_ctor_get(v_x_744_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_815_ == 0)
{
v___x_803_ = v_x_744_;
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_vs_801_);
lean_inc(v_ks_800_);
lean_dec(v_x_744_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; 
v___x_805_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_ks_800_, v_x_746_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_807_; 
if (v_isShared_804_ == 0)
{
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_ks_800_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_vs_801_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v_val_809_; lean_object* v_keys_x27_810_; lean_object* v_vals_x27_811_; lean_object* v___x_813_; 
v_val_809_ = lean_ctor_get(v___x_805_, 0);
lean_inc_n(v_val_809_, 2);
lean_dec_ref(v___x_805_);
v_keys_x27_810_ = l_Array_eraseIdx___redArg(v_ks_800_, v_val_809_);
v_vals_x27_811_ = l_Array_eraseIdx___redArg(v_vs_801_, v_val_809_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_vals_x27_811_);
lean_ctor_set(v___x_803_, 0, v_keys_x27_810_);
v___x_813_ = v___x_803_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_keys_x27_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_vals_x27_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg___boxed(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
size_t v_x_2940__boxed_819_; lean_object* v_res_820_; 
v_x_2940__boxed_819_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_res_820_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_816_, v_x_2940__boxed_819_, v_x_818_);
lean_dec(v_x_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint64_t v___y_824_; 
if (lean_obj_tag(v_x_822_) == 0)
{
uint64_t v___x_827_; 
v___x_827_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_824_ = v___x_827_;
goto v___jp_823_;
}
else
{
uint64_t v_hash_828_; 
v_hash_828_ = lean_ctor_get_uint64(v_x_822_, sizeof(void*)*2);
v___y_824_ = v_hash_828_;
goto v___jp_823_;
}
v___jp_823_:
{
size_t v_h_825_; lean_object* v___x_826_; 
v_h_825_ = lean_uint64_to_usize(v___y_824_);
v___x_826_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_821_, v_h_825_, v_x_822_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_829_, v_x_830_);
lean_dec(v_x_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_832_, lean_object* v_e_833_){
_start:
{
lean_object* v_globalName_x3f_834_; 
v_globalName_x3f_834_ = lean_ctor_get(v_e_833_, 3);
if (lean_obj_tag(v_globalName_x3f_834_) == 0)
{
lean_object* v_keys_835_; lean_object* v_discrTree_836_; lean_object* v_instanceNames_837_; lean_object* v_erased_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_keys_835_ = lean_ctor_get(v_e_833_, 0);
lean_inc_ref(v_keys_835_);
v_discrTree_836_ = lean_ctor_get(v_d_832_, 0);
v_instanceNames_837_ = lean_ctor_get(v_d_832_, 1);
v_erased_838_ = lean_ctor_get(v_d_832_, 2);
v_isSharedCheck_846_ = !lean_is_exclusive(v_d_832_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v_d_832_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_erased_838_);
lean_inc(v_instanceNames_837_);
lean_inc(v_discrTree_836_);
lean_dec(v_d_832_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_836_, v_keys_835_, v_e_833_);
lean_dec_ref(v_keys_835_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_instanceNames_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_erased_838_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_keys_847_; lean_object* v_val_848_; lean_object* v_discrTree_849_; lean_object* v_instanceNames_850_; lean_object* v_erased_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_861_; 
v_keys_847_ = lean_ctor_get(v_e_833_, 0);
v_val_848_ = lean_ctor_get(v_globalName_x3f_834_, 0);
lean_inc(v_val_848_);
v_discrTree_849_ = lean_ctor_get(v_d_832_, 0);
v_instanceNames_850_ = lean_ctor_get(v_d_832_, 1);
v_erased_851_ = lean_ctor_get(v_d_832_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_d_832_);
if (v_isSharedCheck_861_ == 0)
{
v___x_853_ = v_d_832_;
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_erased_851_);
lean_inc(v_instanceNames_850_);
lean_inc(v_discrTree_849_);
lean_dec(v_d_832_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_inc_ref(v_e_833_);
v___x_855_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_849_, v_keys_847_, v_e_833_);
lean_inc(v_val_848_);
v___x_856_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_850_, v_val_848_, v_e_833_);
v___x_857_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_851_, v_val_848_);
lean_dec(v_val_848_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 2, v___x_857_);
lean_ctor_set(v___x_853_, 1, v___x_856_);
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_859_ = v___x_853_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_871_, v_x_872_, v_x_873_);
lean_dec(v_x_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_00_u03b2_879_, v_x_880_, v_x_881_);
lean_dec(v_x_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_x_884_, v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, size_t v_x_890_, size_t v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_889_, v_x_890_, v_x_891_, v_x_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___boxed(lean_object* v_00_u03b2_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
size_t v_x_3165__boxed_901_; size_t v_x_3166__boxed_902_; lean_object* v_res_903_; 
v_x_3165__boxed_901_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_x_3166__boxed_902_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_res_903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(v_00_u03b2_895_, v_x_896_, v_x_3165__boxed_901_, v_x_3166__boxed_902_, v_x_899_, v_x_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, size_t v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_905_, v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___boxed(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
size_t v_x_3182__boxed_913_; lean_object* v_res_914_; 
v_x_3182__boxed_913_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_914_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(v_00_u03b2_909_, v_x_910_, v_x_3182__boxed_913_, v_x_912_);
lean_dec(v_x_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, size_t v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_916_, v_x_917_, v_x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
size_t v_x_3193__boxed_924_; lean_object* v_res_925_; 
v_x_3193__boxed_924_ = lean_unbox_usize(v_x_922_);
lean_dec(v_x_922_);
v_res_925_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_00_u03b2_920_, v_x_921_, v_x_3193__boxed_924_, v_x_923_);
lean_dec(v_x_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
size_t v_x_3204__boxed_939_; size_t v_x_3205__boxed_940_; lean_object* v_res_941_; 
v_x_3204__boxed_939_ = lean_unbox_usize(v_x_935_);
lean_dec(v_x_935_);
v_x_3205__boxed_940_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(v_00_u03b2_933_, v_x_934_, v_x_3204__boxed_939_, v_x_3205__boxed_940_, v_x_937_, v_x_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_942_, lean_object* v_n_943_, lean_object* v_k_944_, lean_object* v_v_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v_n_943_, v_k_944_, v_v_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_947_, size_t v_depth_948_, lean_object* v_keys_949_, lean_object* v_vals_950_, lean_object* v_heq_951_, lean_object* v_i_952_, lean_object* v_entries_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_948_, v_keys_949_, v_vals_950_, v_i_952_, v_entries_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_955_, lean_object* v_depth_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_entries_961_){
_start:
{
size_t v_depth_boxed_962_; lean_object* v_res_963_; 
v_depth_boxed_962_ = lean_unbox_usize(v_depth_956_);
lean_dec(v_depth_956_);
v_res_963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(v_00_u03b2_955_, v_depth_boxed_962_, v_keys_957_, v_vals_958_, v_heq_959_, v_i_960_, v_entries_961_);
lean_dec_ref(v_vals_958_);
lean_dec_ref(v_keys_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_heq_967_, lean_object* v_i_968_, lean_object* v_k_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_965_, v_vals_966_, v_i_968_, v_k_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_k_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_971_, v_keys_972_, v_vals_973_, v_heq_974_, v_i_975_, v_k_976_);
lean_dec(v_k_976_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_978_, lean_object* v_n_979_, lean_object* v_k_980_, lean_object* v_v_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v_n_979_, v_k_980_, v_v_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_983_, size_t v_depth_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_984_, v_keys_985_, v_vals_986_, v_i_988_, v_entries_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_991_, lean_object* v_depth_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_entries_997_){
_start:
{
size_t v_depth_boxed_998_; lean_object* v_res_999_; 
v_depth_boxed_998_ = lean_unbox_usize(v_depth_992_);
lean_dec(v_depth_992_);
v_res_999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_991_, v_depth_boxed_998_, v_keys_993_, v_vals_994_, v_heq_995_, v_i_996_, v_entries_997_);
lean_dec_ref(v_vals_994_);
lean_dec_ref(v_keys_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(lean_object* v_x_1000_, lean_object* v_keys_1001_, lean_object* v_v_1002_, lean_object* v_k_1003_, lean_object* v_as_1004_, lean_object* v_k_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_1000_, v_keys_1001_, v_v_1002_, v_k_1003_, v_as_1004_, v_k_1005_, v_x_1006_, v_x_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___boxed(lean_object* v_x_1011_, lean_object* v_keys_1012_, lean_object* v_v_1013_, lean_object* v_k_1014_, lean_object* v_as_1015_, lean_object* v_k_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(v_x_1011_, v_keys_1012_, v_v_1013_, v_k_1014_, v_as_1015_, v_k_1016_, v_x_1017_, v_x_1018_, v_x_1019_, v_x_1020_);
lean_dec_ref(v_k_1016_);
lean_dec_ref(v_keys_1012_);
lean_dec(v_x_1011_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_x_1023_, v_x_1024_, v_x_1025_, v_x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1029_, v_x_1030_, v_x_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1034_, lean_object* v_declName_1035_){
_start:
{
lean_object* v_discrTree_1036_; lean_object* v_instanceNames_1037_; lean_object* v_erased_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1048_; 
v_discrTree_1036_ = lean_ctor_get(v_d_1034_, 0);
v_instanceNames_1037_ = lean_ctor_get(v_d_1034_, 1);
v_erased_1038_ = lean_ctor_get(v_d_1034_, 2);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_d_1034_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1040_ = v_d_1034_;
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_erased_1038_);
lean_inc(v_instanceNames_1037_);
lean_inc(v_discrTree_1036_);
lean_dec(v_d_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1037_, v_declName_1035_);
v___x_1043_ = lean_box(0);
v___x_1044_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1038_, v_declName_1035_, v___x_1043_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v___x_1044_);
lean_ctor_set(v___x_1040_, 1, v___x_1042_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_discrTree_1036_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1049_, lean_object* v_declName_1050_, lean_object* v_toPure_1051_, lean_object* v_____r_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l_Lean_Meta_Instances_eraseCore(v_d_1049_, v_declName_1050_);
v___x_1054_ = lean_apply_2(v_toPure_1051_, lean_box(0), v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1055_, lean_object* v_____r_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_apply_1(v___f_1055_, v_____r_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_d_1068_, lean_object* v_declName_1069_){
_start:
{
lean_object* v_toApplicative_1070_; lean_object* v_toBind_1071_; lean_object* v_toPure_1072_; lean_object* v_instanceNames_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; uint8_t v___x_1077_; 
v_toApplicative_1070_ = lean_ctor_get(v_inst_1066_, 0);
v_toBind_1071_ = lean_ctor_get(v_inst_1066_, 1);
lean_inc(v_toBind_1071_);
v_toPure_1072_ = lean_ctor_get(v_toApplicative_1070_, 1);
v_instanceNames_1073_ = lean_ctor_get(v_d_1068_, 1);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1072_);
lean_inc_n(v_declName_1069_, 2);
lean_inc_ref(v_d_1068_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1076_, 0, v_d_1068_);
lean_closure_set(v___f_1076_, 1, v_declName_1069_);
lean_closure_set(v___f_1076_, 2, v_toPure_1072_);
lean_inc_ref(v_instanceNames_1073_);
v___x_1077_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1074_, v___x_1075_, v_instanceNames_1073_, v_declName_1069_);
if (v___x_1077_ == 0)
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_d_1068_);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1078_, 0, v___f_1076_);
v___x_1079_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1080_ = l_Lean_MessageData_ofConstName(v_declName_1069_, v___x_1077_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___redArg(v_inst_1066_, v_inst_1067_, v___x_1083_);
v___x_1085_ = lean_apply_4(v_toBind_1071_, lean_box(0), lean_box(0), v___x_1084_, v___f_1078_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_inc(v_toPure_1072_);
lean_dec_ref(v___f_1076_);
lean_dec(v_toBind_1071_);
lean_dec_ref(v_inst_1067_);
lean_dec_ref(v_inst_1066_);
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1068_, v_declName_1069_, v_toPure_1072_, v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_d_1091_, lean_object* v_declName_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1089_, v_inst_1090_, v_d_1091_, v_declName_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t v_level_1094_, lean_object* v_e_1095_){
_start:
{
uint8_t v___y_1097_; uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 2;
v___x_1101_ = l_Lean_instDecidableEqOLeanLevel(v_level_1094_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v_globalName_x3f_1102_; 
v_globalName_x3f_1102_ = lean_ctor_get(v_e_1095_, 3);
lean_inc(v_globalName_x3f_1102_);
if (lean_obj_tag(v_globalName_x3f_1102_) == 0)
{
v___y_1097_ = v___x_1101_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
v_val_1103_ = lean_ctor_get(v_globalName_x3f_1102_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_globalName_x3f_1102_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v_globalName_x3f_1102_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v_globalName_x3f_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_isPrivateName(v_val_1103_);
lean_dec(v_val_1103_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1109_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_e_1095_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_e_1095_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
else
{
lean_del_object(v___x_1105_);
v___y_1097_ = v___x_1101_;
goto v___jp_1096_;
}
}
}
}
else
{
v___y_1097_ = v___x_1101_;
goto v___jp_1096_;
}
v___jp_1096_:
{
if (v___y_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref(v_e_1095_);
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_e_1095_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_level_1112_, lean_object* v_e_1113_){
_start:
{
uint8_t v_level_boxed_1114_; lean_object* v_res_1115_; 
v_level_boxed_1114_ = lean_unbox(v_level_1112_);
v_res_1115_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v_level_boxed_1114_, v_e_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object* v___y_1116_){
_start:
{
lean_inc_ref(v___y_1116_);
return v___y_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v___y_1117_);
lean_dec_ref(v___y_1117_);
return v_res_1118_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_1132_ = lean_obj_once(&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1133_ = lean_obj_once(&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
lean_ctor_set(v___x_1134_, 2, v___x_1131_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___f_1135_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___f_1136_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1137_ = lean_obj_once(&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1138_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1139_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1137_);
lean_ctor_set(v___x_1140_, 3, v___f_1136_);
lean_ctor_set(v___x_1140_, 4, v___f_1135_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1143_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1146_, uint8_t v_allowLevelAssignments_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1147_, v_k_1146_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1170_, lean_object* v_allowLevelAssignments_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1177_; lean_object* v_res_1178_; 
v_allowLevelAssignments_boxed_1177_ = lean_unbox(v_allowLevelAssignments_1171_);
v_res_1178_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1170_, v_allowLevelAssignments_boxed_1177_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1179_, lean_object* v_k_1180_, uint8_t v_allowLevelAssignments_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1180_, v_allowLevelAssignments_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_k_1189_, lean_object* v_allowLevelAssignments_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1196_; lean_object* v_res_1197_; 
v_allowLevelAssignments_boxed_1196_ = lean_unbox(v_allowLevelAssignments_1190_);
v_res_1197_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1188_, v_k_1189_, v_allowLevelAssignments_boxed_1196_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1198_, lean_object* v___x_1199_, uint8_t v___x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1198_, v___x_1199_, v___x_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v_snd_1208_; lean_object* v_snd_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v_snd_1208_ = lean_ctor_get(v_a_1207_, 1);
lean_inc(v_snd_1208_);
lean_dec(v_a_1207_);
v_snd_1209_ = lean_ctor_get(v_snd_1208_, 1);
lean_inc(v_snd_1209_);
lean_dec(v_snd_1208_);
v___x_1210_ = 0;
v___x_1211_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1209_, v___x_1210_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
return v___x_1211_;
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1206_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1206_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v___x_497__boxed_1228_; lean_object* v_res_1229_; 
v___x_497__boxed_1228_ = lean_unbox(v___x_1222_);
v_res_1229_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1220_, v___x_1221_, v___x_497__boxed_1228_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1236_; 
lean_inc(v_a_1234_);
lean_inc_ref(v_a_1233_);
lean_inc(v_a_1232_);
lean_inc_ref(v_a_1231_);
v___x_1236_ = lean_infer_type(v_e_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = 0;
v___x_1240_ = lean_box(v___x_1239_);
v___f_1241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1241_, 0, v_a_1237_);
lean_closure_set(v___f_1241_, 1, v___x_1238_);
lean_closure_set(v___f_1241_, 2, v___x_1240_);
v___x_1242_ = 0;
v___x_1243_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1241_, v___x_1242_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1236_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1236_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1259_, lean_object* v_b_1260_, lean_object* v_c_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
v___x_1267_ = lean_apply_7(v_k_1259_, v_b_1260_, v_c_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, lean_box(0));
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1268_, lean_object* v_b_1269_, lean_object* v_c_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1268_, v_b_1269_, v_c_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1277_, lean_object* v_k_1278_, uint8_t v_cleanupAnnotations_1279_, uint8_t v_whnfType_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___f_1286_; lean_object* v___x_1287_; 
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1286_, 0, v_k_1278_);
v___x_1287_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1277_, v___f_1286_, v_cleanupAnnotations_1279_, v_whnfType_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
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
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1287_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1287_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1304_, lean_object* v_k_1305_, lean_object* v_cleanupAnnotations_1306_, lean_object* v_whnfType_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1313_; uint8_t v_whnfType_boxed_1314_; lean_object* v_res_1315_; 
v_cleanupAnnotations_boxed_1313_ = lean_unbox(v_cleanupAnnotations_1306_);
v_whnfType_boxed_1314_ = lean_unbox(v_whnfType_1307_);
v_res_1315_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1304_, v_k_1305_, v_cleanupAnnotations_boxed_1313_, v_whnfType_boxed_1314_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1316_, lean_object* v_type_1317_, lean_object* v_k_1318_, uint8_t v_cleanupAnnotations_1319_, uint8_t v_whnfType_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1317_, v_k_1318_, v_cleanupAnnotations_1319_, v_whnfType_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_type_1328_, lean_object* v_k_1329_, lean_object* v_cleanupAnnotations_1330_, lean_object* v_whnfType_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1337_; uint8_t v_whnfType_boxed_1338_; lean_object* v_res_1339_; 
v_cleanupAnnotations_boxed_1337_ = lean_unbox(v_cleanupAnnotations_1330_);
v_whnfType_boxed_1338_ = lean_unbox(v_whnfType_1331_);
v_res_1339_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1327_, v_type_1328_, v_k_1329_, v_cleanupAnnotations_boxed_1337_, v_whnfType_boxed_1338_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_b_1346_);
return v___x_1353_;
}
else
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1407_; 
v_fst_1354_ = lean_ctor_get(v_b_1346_, 0);
v_snd_1355_ = lean_ctor_get(v_b_1346_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_b_1346_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1357_ = v_b_1346_;
v_isShared_1358_ = v_isSharedCheck_1407_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v_b_1346_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1407_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_next_1364_; 
v_next_1364_ = lean_ctor_get(v_snd_1355_, 0);
lean_inc(v_next_1364_);
if (lean_obj_tag(v_next_1364_) == 0)
{
goto v___jp_1359_;
}
else
{
lean_object* v_upperBound_1365_; lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1406_; 
v_upperBound_1365_ = lean_ctor_get(v_snd_1355_, 1);
v_val_1366_ = lean_ctor_get(v_next_1364_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_next_1364_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1368_ = v_next_1364_;
v_isShared_1369_ = v_isSharedCheck_1406_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v_next_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1406_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_nat_dec_lt(v_val_1366_, v_upperBound_1365_);
if (v___x_1370_ == 0)
{
lean_del_object(v___x_1368_);
lean_dec(v_val_1366_);
goto v___jp_1359_;
}
else
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1403_; 
lean_inc(v_upperBound_1365_);
lean_del_object(v___x_1357_);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_snd_1355_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1404_ = lean_ctor_get(v_snd_1355_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_snd_1355_, 0);
lean_dec(v_unused_1405_);
v___x_1372_ = v_snd_1355_;
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v_snd_1355_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1403_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_array_uget_borrowed(v_as_1343_, v_i_1345_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v_a_1374_);
v___x_1375_ = lean_infer_type(v_a_1374_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_a_1378_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_val_1366_, v___x_1382_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1383_);
v___x_1385_ = v___x_1368_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1384_;
}
v___jp_1377_:
{
size_t v___x_1379_; size_t v___x_1380_; 
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1345_, v___x_1379_);
v_i_1345_ = v___x_1380_;
v_b_1346_ = v_a_1378_;
goto _start;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1385_);
v___x_1387_ = v___x_1372_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_upperBound_1365_);
v___x_1387_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1389_ = l_Lean_Expr_isAppOf(v_a_1376_, v___x_1388_);
lean_dec(v_a_1376_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_val_1366_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_fst_1354_);
lean_ctor_set(v___x_1390_, 1, v___x_1387_);
v_a_1378_ = v___x_1390_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_array_push(v_fst_1354_, v_val_1366_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___x_1387_);
v_a_1378_ = v___x_1392_;
goto v___jp_1377_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1372_);
lean_del_object(v___x_1368_);
lean_dec(v_val_1366_);
lean_dec(v_upperBound_1365_);
lean_dec(v_fst_1354_);
v_a_1395_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1375_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1375_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; 
if (v_isShared_1358_ == 0)
{
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1354_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_snd_1355_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1408_, lean_object* v_sz_1409_, lean_object* v_i_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1409_);
lean_dec(v_sz_1409_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1410_);
lean_dec(v_i_1410_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1408_, v_sz_boxed_1417_, v_i_boxed_1418_, v_b_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v_as_1408_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1424_, lean_object* v_args_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; lean_object* v___y_1434_; lean_object* v_env_1459_; lean_object* v___x_1460_; 
v___x_1432_ = lean_st_ref_get(v___y_1430_);
v_env_1459_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_env_1459_);
lean_dec(v___x_1432_);
v___x_1460_ = l_Lean_getOutParamPositions_x3f(v_env_1459_, v_declName_1424_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1434_ = v___x_1461_;
goto v___jp_1433_;
}
else
{
lean_object* v_val_1462_; 
v_val_1462_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1462_);
lean_dec_ref(v___x_1460_);
v___y_1434_ = v_val_1462_;
goto v___jp_1433_;
}
v___jp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; size_t v_sz_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v___x_1435_ = lean_array_get_size(v_args_1425_);
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___y_1434_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v_sz_1439_ = lean_array_size(v_args_1425_);
v___x_1440_ = ((size_t)0ULL);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1425_, v_sz_1439_, v___x_1440_, v___x_1438_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_fst_1446_; lean_object* v___x_1448_; 
v_fst_1446_ = lean_ctor_get(v_a_1442_, 0);
lean_inc(v_fst_1446_);
lean_dec(v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_fst_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_fst_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1441_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1441_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1463_, lean_object* v_args_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1463_, v_args_1464_, v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_x_1465_);
lean_dec_ref(v_args_1464_);
lean_dec(v_declName_1463_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Expr_getAppFn(v_classTy_1472_);
if (lean_obj_tag(v___x_1478_) == 4)
{
lean_object* v_declName_1479_; lean_object* v___x_1480_; 
v_declName_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_declName_1479_);
lean_inc(v_a_1476_);
lean_inc_ref(v_a_1475_);
lean_inc(v_a_1474_);
lean_inc_ref(v_a_1473_);
v___x_1480_ = lean_infer_type(v___x_1478_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___f_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1480_);
v___f_1482_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1482_, 0, v_declName_1479_);
v___x_1483_ = 0;
v___x_1484_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1481_, v___f_1482_, v___x_1483_, v___x_1483_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
return v___x_1484_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_declName_1479_);
v_a_1485_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1480_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1480_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref(v___x_1478_);
v___x_1493_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec_ref(v_classTy_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_ks_1506_; lean_object* v_vs_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1531_; 
v_ks_1506_ = lean_ctor_get(v_x_1502_, 0);
v_vs_1507_ = lean_ctor_get(v_x_1502_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1502_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1509_ = v_x_1502_;
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_vs_1507_);
lean_inc(v_ks_1506_);
lean_dec(v_x_1502_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_array_get_size(v_ks_1506_);
v___x_1512_ = lean_nat_dec_lt(v_x_1503_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_dec(v_x_1503_);
v___x_1513_ = lean_array_push(v_ks_1506_, v_x_1504_);
v___x_1514_ = lean_array_push(v_vs_1507_, v_x_1505_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v___x_1514_);
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1516_ = v___x_1509_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
else
{
lean_object* v_k_x27_1518_; uint8_t v___x_1519_; 
v_k_x27_1518_ = lean_array_fget_borrowed(v_ks_1506_, v_x_1503_);
v___x_1519_ = l_Lean_instBEqMVarId_beq(v_x_1504_, v_k_x27_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1521_; 
if (v_isShared_1510_ == 0)
{
v___x_1521_ = v___x_1509_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_ks_1506_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_vs_1507_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_add(v_x_1503_, v___x_1522_);
lean_dec(v_x_1503_);
v_x_1502_ = v___x_1521_;
v_x_1503_ = v___x_1523_;
goto _start;
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1526_ = lean_array_fset(v_ks_1506_, v_x_1503_, v_x_1504_);
v___x_1527_ = lean_array_fset(v_vs_1507_, v_x_1503_, v_x_1505_);
lean_dec(v_x_1503_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v___x_1527_);
lean_ctor_set(v___x_1509_, 0, v___x_1526_);
v___x_1529_ = v___x_1509_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_1532_, lean_object* v_k_1533_, lean_object* v_v_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_1532_, v___x_1535_, v_k_1533_, v_v_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1537_, size_t v_x_1538_, size_t v_x_1539_, lean_object* v_x_1540_, lean_object* v_x_1541_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v_es_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; lean_object* v_j_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_es_1542_ = lean_ctor_get(v_x_1537_, 0);
v___x_1543_ = ((size_t)5ULL);
v___x_1544_ = ((size_t)1ULL);
v___x_1545_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_1546_ = lean_usize_land(v_x_1538_, v___x_1545_);
v_j_1547_ = lean_usize_to_nat(v___x_1546_);
v___x_1548_ = lean_array_get_size(v_es_1542_);
v___x_1549_ = lean_nat_dec_lt(v_j_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_dec(v_j_1547_);
lean_dec(v_x_1541_);
lean_dec(v_x_1540_);
return v_x_1537_;
}
else
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1586_; 
lean_inc_ref(v_es_1542_);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_x_1537_, 0);
lean_dec(v_unused_1587_);
v___x_1551_ = v_x_1537_;
v_isShared_1552_ = v_isSharedCheck_1586_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v_x_1537_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1586_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_v_1553_; lean_object* v___x_1554_; lean_object* v_xs_x27_1555_; lean_object* v___y_1557_; 
v_v_1553_ = lean_array_fget(v_es_1542_, v_j_1547_);
v___x_1554_ = lean_box(0);
v_xs_x27_1555_ = lean_array_fset(v_es_1542_, v_j_1547_, v___x_1554_);
switch(lean_obj_tag(v_v_1553_))
{
case 0:
{
lean_object* v_key_1562_; lean_object* v_val_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
v_key_1562_ = lean_ctor_get(v_v_1553_, 0);
v_val_1563_ = lean_ctor_get(v_v_1553_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_v_1553_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1565_ = v_v_1553_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_val_1563_);
lean_inc(v_key_1562_);
lean_dec(v_v_1553_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_instBEqMVarId_beq(v_x_1540_, v_key_1562_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_del_object(v___x_1565_);
v___x_1568_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1562_, v_val_1563_, v_x_1540_, v_x_1541_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
v___y_1557_ = v___x_1569_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1571_; 
lean_dec(v_val_1563_);
lean_dec(v_key_1562_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v_x_1541_);
lean_ctor_set(v___x_1565_, 0, v_x_1540_);
v___x_1571_ = v___x_1565_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_x_1540_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_x_1541_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
v___y_1557_ = v___x_1571_;
goto v___jp_1556_;
}
}
}
}
case 1:
{
lean_object* v_node_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1584_; 
v_node_1574_ = lean_ctor_get(v_v_1553_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_v_1553_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1576_ = v_v_1553_;
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_node_1574_);
lean_dec(v_v_1553_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
size_t v___x_1578_; size_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1578_ = lean_usize_shift_right(v_x_1538_, v___x_1543_);
v___x_1579_ = lean_usize_add(v_x_1539_, v___x_1544_);
v___x_1580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_node_1574_, v___x_1578_, v___x_1579_, v_x_1540_, v_x_1541_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1580_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
v___y_1557_ = v___x_1582_;
goto v___jp_1556_;
}
}
}
default: 
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_x_1540_);
lean_ctor_set(v___x_1585_, 1, v_x_1541_);
v___y_1557_ = v___x_1585_;
goto v___jp_1556_;
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_array_fset(v_xs_x27_1555_, v_j_1547_, v___y_1557_);
lean_dec(v_j_1547_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1558_);
v___x_1560_ = v___x_1551_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
else
{
lean_object* v_ks_1588_; lean_object* v_vs_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1609_; 
v_ks_1588_ = lean_ctor_get(v_x_1537_, 0);
v_vs_1589_ = lean_ctor_get(v_x_1537_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1591_ = v_x_1537_;
v_isShared_1592_ = v_isSharedCheck_1609_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_vs_1589_);
lean_inc(v_ks_1588_);
lean_dec(v_x_1537_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1609_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_ks_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_vs_1589_);
v___x_1594_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v_newNode_1595_; uint8_t v___y_1597_; size_t v___x_1603_; uint8_t v___x_1604_; 
v_newNode_1595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v___x_1594_, v_x_1540_, v_x_1541_);
v___x_1603_ = ((size_t)7ULL);
v___x_1604_ = lean_usize_dec_le(v___x_1603_, v_x_1539_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1595_);
v___x_1606_ = lean_unsigned_to_nat(4u);
v___x_1607_ = lean_nat_dec_lt(v___x_1605_, v___x_1606_);
lean_dec(v___x_1605_);
v___y_1597_ = v___x_1607_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___x_1604_;
goto v___jp_1596_;
}
v___jp_1596_:
{
if (v___y_1597_ == 0)
{
lean_object* v_ks_1598_; lean_object* v_vs_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_ks_1598_ = lean_ctor_get(v_newNode_1595_, 0);
lean_inc_ref(v_ks_1598_);
v_vs_1599_ = lean_ctor_get(v_newNode_1595_, 1);
lean_inc_ref(v_vs_1599_);
lean_dec_ref(v_newNode_1595_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_1602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1539_, v_ks_1598_, v_vs_1599_, v___x_1600_, v___x_1601_);
lean_dec_ref(v_vs_1599_);
lean_dec_ref(v_ks_1598_);
return v___x_1602_;
}
else
{
return v_newNode_1595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_1610_, lean_object* v_keys_1611_, lean_object* v_vals_1612_, lean_object* v_i_1613_, lean_object* v_entries_1614_){
_start:
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_array_get_size(v_keys_1611_);
v___x_1616_ = lean_nat_dec_lt(v_i_1613_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_dec(v_i_1613_);
return v_entries_1614_;
}
else
{
lean_object* v_k_1617_; lean_object* v_v_1618_; uint64_t v___x_1619_; size_t v_h_1620_; size_t v___x_1621_; lean_object* v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; size_t v___x_1625_; size_t v_h_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_k_1617_ = lean_array_fget_borrowed(v_keys_1611_, v_i_1613_);
v_v_1618_ = lean_array_fget_borrowed(v_vals_1612_, v_i_1613_);
v___x_1619_ = l_Lean_instHashableMVarId_hash(v_k_1617_);
v_h_1620_ = lean_uint64_to_usize(v___x_1619_);
v___x_1621_ = ((size_t)5ULL);
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_sub(v_depth_1610_, v___x_1623_);
v___x_1625_ = lean_usize_mul(v___x_1621_, v___x_1624_);
v_h_1626_ = lean_usize_shift_right(v_h_1620_, v___x_1625_);
v___x_1627_ = lean_nat_add(v_i_1613_, v___x_1622_);
lean_dec(v_i_1613_);
lean_inc(v_v_1618_);
lean_inc(v_k_1617_);
v___x_1628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_entries_1614_, v_h_1626_, v_depth_1610_, v_k_1617_, v_v_1618_);
v_i_1613_ = v___x_1627_;
v_entries_1614_ = v___x_1628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_1630_, lean_object* v_keys_1631_, lean_object* v_vals_1632_, lean_object* v_i_1633_, lean_object* v_entries_1634_){
_start:
{
size_t v_depth_boxed_1635_; lean_object* v_res_1636_; 
v_depth_boxed_1635_ = lean_unbox_usize(v_depth_1630_);
lean_dec(v_depth_1630_);
v_res_1636_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_1635_, v_keys_1631_, v_vals_1632_, v_i_1633_, v_entries_1634_);
lean_dec_ref(v_vals_1632_);
lean_dec_ref(v_keys_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
size_t v_x_1574__boxed_1642_; size_t v_x_1575__boxed_1643_; lean_object* v_res_1644_; 
v_x_1574__boxed_1642_ = lean_unbox_usize(v_x_1638_);
lean_dec(v_x_1638_);
v_x_1575__boxed_1643_ = lean_unbox_usize(v_x_1639_);
lean_dec(v_x_1639_);
v_res_1644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1637_, v_x_1574__boxed_1642_, v_x_1575__boxed_1643_, v_x_1640_, v_x_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
uint64_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1648_ = l_Lean_instHashableMVarId_hash(v_x_1646_);
v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
v___x_1650_ = ((size_t)1ULL);
v___x_1651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1645_, v___x_1649_, v___x_1650_, v_x_1646_, v_x_1647_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(lean_object* v_mvarId_1652_, lean_object* v_val_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_mctx_1657_; lean_object* v_cache_1658_; lean_object* v_zetaDeltaFVarIds_1659_; lean_object* v_postponed_1660_; lean_object* v_diag_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1689_; 
v___x_1656_ = lean_st_ref_take(v___y_1654_);
v_mctx_1657_ = lean_ctor_get(v___x_1656_, 0);
v_cache_1658_ = lean_ctor_get(v___x_1656_, 1);
v_zetaDeltaFVarIds_1659_ = lean_ctor_get(v___x_1656_, 2);
v_postponed_1660_ = lean_ctor_get(v___x_1656_, 3);
v_diag_1661_ = lean_ctor_get(v___x_1656_, 4);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1663_ = v___x_1656_;
v_isShared_1664_ = v_isSharedCheck_1689_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_diag_1661_);
lean_inc(v_postponed_1660_);
lean_inc(v_zetaDeltaFVarIds_1659_);
lean_inc(v_cache_1658_);
lean_inc(v_mctx_1657_);
lean_dec(v___x_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1689_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_depth_1665_; lean_object* v_levelAssignDepth_1666_; lean_object* v_lmvarCounter_1667_; lean_object* v_mvarCounter_1668_; lean_object* v_lDecls_1669_; lean_object* v_decls_1670_; lean_object* v_userNames_1671_; lean_object* v_lAssignment_1672_; lean_object* v_eAssignment_1673_; lean_object* v_dAssignment_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1688_; 
v_depth_1665_ = lean_ctor_get(v_mctx_1657_, 0);
v_levelAssignDepth_1666_ = lean_ctor_get(v_mctx_1657_, 1);
v_lmvarCounter_1667_ = lean_ctor_get(v_mctx_1657_, 2);
v_mvarCounter_1668_ = lean_ctor_get(v_mctx_1657_, 3);
v_lDecls_1669_ = lean_ctor_get(v_mctx_1657_, 4);
v_decls_1670_ = lean_ctor_get(v_mctx_1657_, 5);
v_userNames_1671_ = lean_ctor_get(v_mctx_1657_, 6);
v_lAssignment_1672_ = lean_ctor_get(v_mctx_1657_, 7);
v_eAssignment_1673_ = lean_ctor_get(v_mctx_1657_, 8);
v_dAssignment_1674_ = lean_ctor_get(v_mctx_1657_, 9);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_mctx_1657_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1676_ = v_mctx_1657_;
v_isShared_1677_ = v_isSharedCheck_1688_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_dAssignment_1674_);
lean_inc(v_eAssignment_1673_);
lean_inc(v_lAssignment_1672_);
lean_inc(v_userNames_1671_);
lean_inc(v_decls_1670_);
lean_inc(v_lDecls_1669_);
lean_inc(v_mvarCounter_1668_);
lean_inc(v_lmvarCounter_1667_);
lean_inc(v_levelAssignDepth_1666_);
lean_inc(v_depth_1665_);
lean_dec(v_mctx_1657_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1688_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_eAssignment_1673_, v_mvarId_1652_, v_val_1653_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 8, v___x_1678_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_depth_1665_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_levelAssignDepth_1666_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_lmvarCounter_1667_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_mvarCounter_1668_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_lDecls_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v_decls_1670_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_userNames_1671_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_lAssignment_1672_);
lean_ctor_set(v_reuseFailAlloc_1687_, 8, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 9, v_dAssignment_1674_);
v___x_1680_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1680_);
v___x_1682_ = v___x_1663_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_cache_1658_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_zetaDeltaFVarIds_1659_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_postponed_1660_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_diag_1661_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_st_ref_set(v___y_1654_, v___x_1682_);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg___boxed(lean_object* v_mvarId_1690_, lean_object* v_val_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1690_, v_val_1691_, v___y_1692_);
lean_dec(v___y_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(lean_object* v_a_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = l_Lean_Expr_mvarId_x21(v_x_1696_);
v___x_1698_ = l_Lean_instBEqMVarId_beq(v___x_1697_, v_a_1695_);
lean_dec(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed(lean_object* v_a_1699_, lean_object* v_x_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(v_a_1699_, v_x_1700_);
lean_dec_ref(v_x_1700_);
lean_dec(v_a_1699_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_argMVars_1703_, lean_object* v_argVars_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_b_1708_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v_a_1717_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1716_ = lean_box(0);
v_a_1717_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
lean_inc(v_a_1717_);
v___f_1738_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1738_, 0, v_a_1717_);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = l_Array_findIdx_x3f_loop___redArg(v___f_1738_, v_argMVars_1703_, v___x_1739_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = l_Lean_instInhabitedExpr;
v___x_1743_ = lean_array_get_borrowed(v___x_1742_, v_argVars_1704_, v_val_1741_);
lean_dec(v_val_1741_);
lean_inc(v___x_1743_);
lean_inc(v_a_1717_);
v___x_1744_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_a_1717_, v___x_1743_, v___y_1710_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_dec_ref(v___x_1744_);
v___y_1719_ = v___y_1709_;
v___y_1720_ = v___y_1710_;
v___y_1721_ = v___y_1711_;
v___y_1722_ = v___y_1712_;
goto v___jp_1718_;
}
else
{
return v___x_1744_;
}
}
else
{
lean_dec(v___x_1740_);
v___y_1719_ = v___y_1709_;
v___y_1720_ = v___y_1710_;
v___y_1721_ = v___y_1711_;
v___y_1722_ = v___y_1712_;
goto v___jp_1718_;
}
v___jp_1718_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_inc(v_a_1717_);
v___x_1723_ = l_Lean_Expr_mvar___override(v_a_1717_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
v___x_1724_ = lean_infer_type(v___x_1723_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1703_, v_argVars_1704_, v_a_1725_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1726_) == 0)
{
size_t v___x_1727_; size_t v___x_1728_; 
lean_dec_ref(v___x_1726_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_add(v_i_1707_, v___x_1727_);
v_i_1707_ = v___x_1728_;
v_b_1708_ = v___x_1716_;
goto _start;
}
else
{
return v___x_1726_;
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1724_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1724_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1745_, lean_object* v_argVars_1746_, lean_object* v_e_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Meta_getMVars(v_e_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_box(0);
v_sz_1756_ = lean_array_size(v_a_1754_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1745_, v_argVars_1746_, v_a_1754_, v_sz_1756_, v___x_1757_, v___x_1755_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1754_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1766_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1755_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1755_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
return v___x_1758_;
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1753_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1753_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1775_, lean_object* v_argVars_1776_, lean_object* v_e_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1775_, v_argVars_1776_, v_e_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_argVars_1776_);
lean_dec_ref(v_argMVars_1775_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_argMVars_1784_, lean_object* v_argVars_1785_, lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; lean_object* v_res_1797_; 
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1784_, v_argVars_1785_, v_as_1786_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_as_1786_);
lean_dec_ref(v_argVars_1785_);
lean_dec_ref(v_argMVars_1784_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_mvarId_1798_, lean_object* v_val_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1798_, v_val_1799_, v___y_1801_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_mvarId_1806_, lean_object* v_val_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_mvarId_1806_, v_val_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_x_1815_, v_x_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1819_, lean_object* v_x_1820_, size_t v_x_1821_, size_t v_x_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1820_, v_x_1821_, v_x_1822_, v_x_1823_, v_x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
size_t v_x_1946__boxed_1832_; size_t v_x_1947__boxed_1833_; lean_object* v_res_1834_; 
v_x_1946__boxed_1832_ = lean_unbox_usize(v_x_1828_);
lean_dec(v_x_1828_);
v_x_1947__boxed_1833_ = lean_unbox_usize(v_x_1829_);
lean_dec(v_x_1829_);
v_res_1834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(v_00_u03b2_1826_, v_x_1827_, v_x_1946__boxed_1832_, v_x_1947__boxed_1833_, v_x_1830_, v_x_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1835_, lean_object* v_n_1836_, lean_object* v_k_1837_, lean_object* v_v_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1836_, v_k_1837_, v_v_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1840_, size_t v_depth_1841_, lean_object* v_keys_1842_, lean_object* v_vals_1843_, lean_object* v_heq_1844_, lean_object* v_i_1845_, lean_object* v_entries_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1841_, v_keys_1842_, v_vals_1843_, v_i_1845_, v_entries_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1848_, lean_object* v_depth_1849_, lean_object* v_keys_1850_, lean_object* v_vals_1851_, lean_object* v_heq_1852_, lean_object* v_i_1853_, lean_object* v_entries_1854_){
_start:
{
size_t v_depth_boxed_1855_; lean_object* v_res_1856_; 
v_depth_boxed_1855_ = lean_unbox_usize(v_depth_1849_);
lean_dec(v_depth_1849_);
v_res_1856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1848_, v_depth_boxed_1855_, v_keys_1850_, v_vals_1851_, v_heq_1852_, v_i_1853_, v_entries_1854_);
lean_dec_ref(v_vals_1851_);
lean_dec_ref(v_keys_1850_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_1858_, v_x_1859_, v_x_1860_, v_x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v___x_1866_; 
v___x_1866_ = l_Lean_Expr_hasMVar(v_e_1863_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_e_1863_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v_mctx_1869_; lean_object* v___x_1870_; lean_object* v_fst_1871_; lean_object* v_snd_1872_; lean_object* v___x_1873_; lean_object* v_cache_1874_; lean_object* v_zetaDeltaFVarIds_1875_; lean_object* v_postponed_1876_; lean_object* v_diag_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1886_; 
v___x_1868_ = lean_st_ref_get(v___y_1864_);
v_mctx_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_mctx_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Lean_instantiateMVarsCore(v_mctx_1869_, v_e_1863_);
v_fst_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_fst_1871_);
v_snd_1872_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_snd_1872_);
lean_dec_ref(v___x_1870_);
v___x_1873_ = lean_st_ref_take(v___y_1864_);
v_cache_1874_ = lean_ctor_get(v___x_1873_, 1);
v_zetaDeltaFVarIds_1875_ = lean_ctor_get(v___x_1873_, 2);
v_postponed_1876_ = lean_ctor_get(v___x_1873_, 3);
v_diag_1877_ = lean_ctor_get(v___x_1873_, 4);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1873_, 0);
lean_dec(v_unused_1887_);
v___x_1879_ = v___x_1873_;
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_diag_1877_);
lean_inc(v_postponed_1876_);
lean_inc(v_zetaDeltaFVarIds_1875_);
lean_inc(v_cache_1874_);
lean_dec(v___x_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_snd_1872_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_snd_1872_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_zetaDeltaFVarIds_1875_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_postponed_1876_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v_diag_1877_);
v___x_1882_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_st_ref_set(v___y_1864_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_fst_1871_);
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1888_, v___y_1889_);
lean_dec(v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1892_, v___y_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1906_, lean_object* v_opt_1907_){
_start:
{
lean_object* v_name_1908_; lean_object* v_defValue_1909_; lean_object* v_map_1910_; lean_object* v___x_1911_; 
v_name_1908_ = lean_ctor_get(v_opt_1907_, 0);
v_defValue_1909_ = lean_ctor_get(v_opt_1907_, 1);
v_map_1910_ = lean_ctor_get(v_opts_1906_, 0);
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1910_, v_name_1908_);
if (lean_obj_tag(v___x_1911_) == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_unbox(v_defValue_1909_);
return v___x_1912_;
}
else
{
lean_object* v_val_1913_; 
v_val_1913_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v___x_1911_);
if (lean_obj_tag(v_val_1913_) == 1)
{
uint8_t v_v_1914_; 
v_v_1914_ = lean_ctor_get_uint8(v_val_1913_, 0);
lean_dec_ref(v_val_1913_);
return v_v_1914_;
}
else
{
uint8_t v___x_1915_; 
lean_dec(v_val_1913_);
v___x_1915_ = lean_unbox(v_defValue_1909_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1916_, lean_object* v_opt_1917_){
_start:
{
uint8_t v_res_1918_; lean_object* v_r_1919_; 
v_res_1918_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1916_, v_opt_1917_);
lean_dec_ref(v_opt_1917_);
lean_dec_ref(v_opts_1916_);
v_r_1919_ = lean_box(v_res_1918_);
return v_r_1919_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1920_, lean_object* v_as_1921_, size_t v_i_1922_, size_t v_stop_1923_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_eq(v_i_1922_, v_stop_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = lean_array_uget_borrowed(v_as_1921_, v_i_1922_);
v___x_1926_ = lean_nat_dec_eq(v_a_1920_, v___x_1925_);
if (v___x_1926_ == 0)
{
size_t v___x_1927_; size_t v___x_1928_; 
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_i_1922_, v___x_1927_);
v_i_1922_ = v___x_1928_;
goto _start;
}
else
{
return v___x_1926_;
}
}
else
{
uint8_t v___x_1930_; 
v___x_1930_ = 0;
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1931_, lean_object* v_as_1932_, lean_object* v_i_1933_, lean_object* v_stop_1934_){
_start:
{
size_t v_i_boxed_1935_; size_t v_stop_boxed_1936_; uint8_t v_res_1937_; lean_object* v_r_1938_; 
v_i_boxed_1935_ = lean_unbox_usize(v_i_1933_);
lean_dec(v_i_1933_);
v_stop_boxed_1936_ = lean_unbox_usize(v_stop_1934_);
lean_dec(v_stop_1934_);
v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1931_, v_as_1932_, v_i_boxed_1935_, v_stop_boxed_1936_);
lean_dec_ref(v_as_1932_);
lean_dec(v_a_1931_);
v_r_1938_ = lean_box(v_res_1937_);
return v_r_1938_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_array_get_size(v_as_1939_);
v___x_1943_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
return v___x_1943_;
}
else
{
if (v___x_1943_ == 0)
{
return v___x_1943_;
}
else
{
size_t v___x_1944_; size_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = lean_usize_of_nat(v___x_1942_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1940_, v_as_1939_, v___x_1944_, v___x_1945_);
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1947_, lean_object* v_a_1948_){
_start:
{
uint8_t v_res_1949_; lean_object* v_r_1950_; 
v_res_1949_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_as_1947_);
v_r_1950_ = lean_box(v_res_1949_);
return v_r_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1951_, lean_object* v_fst_1952_, lean_object* v_argVars_1953_, lean_object* v_as_1954_, size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_a_1964_; uint8_t v___x_1968_; 
v___x_1968_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_b_1957_);
return v___x_1969_;
}
else
{
lean_object* v_next_1970_; 
v_next_1970_ = lean_ctor_get(v_b_1957_, 0);
lean_inc(v_next_1970_);
if (lean_obj_tag(v_next_1970_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_b_1957_);
return v___x_1971_;
}
else
{
lean_object* v_upperBound_1972_; lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2004_; 
v_upperBound_1972_ = lean_ctor_get(v_b_1957_, 1);
v_val_1973_ = lean_ctor_get(v_next_1970_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_next_1970_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1975_ = v_next_1970_;
v_isShared_1976_ = v_isSharedCheck_2004_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_dec(v_next_1970_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2004_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_lt(v_val_1973_, v_upperBound_1972_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_del_object(v___x_1975_);
lean_dec(v_val_1973_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_b_1957_);
return v___x_1978_;
}
else
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2001_; 
lean_inc(v_upperBound_1972_);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_b_1957_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; 
v_unused_2002_ = lean_ctor_get(v_b_1957_, 1);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_b_1957_, 0);
lean_dec(v_unused_2003_);
v___x_1980_ = v_b_1957_;
v_isShared_1981_ = v_isSharedCheck_2001_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_b_1957_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2001_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_val_1973_, v___x_1982_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1983_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1985_);
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_upperBound_1972_);
v___x_1987_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1951_, v_val_1973_);
lean_dec(v_val_1973_);
if (v___x_1988_ == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_array_uget_borrowed(v_as_1954_, v_i_1956_);
lean_inc(v_a_1989_);
v___x_1990_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1952_, v_argVars_1953_, v_a_1989_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_dec_ref(v___x_1990_);
v_a_1964_ = v___x_1987_;
goto v___jp_1963_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v___x_1987_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
v_a_1964_ = v___x_1987_;
goto v___jp_1963_;
}
}
}
}
}
}
}
}
v___jp_1963_:
{
size_t v___x_1965_; size_t v___x_1966_; 
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1956_, v___x_1965_);
v_i_1956_ = v___x_1966_;
v_b_1957_ = v_a_1964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2005_, lean_object* v_fst_2006_, lean_object* v_argVars_2007_, lean_object* v_as_2008_, lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
size_t v_sz_boxed_2017_; size_t v_i_boxed_2018_; lean_object* v_res_2019_; 
v_sz_boxed_2017_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2005_, v_fst_2006_, v_argVars_2007_, v_as_2008_, v_sz_boxed_2017_, v_i_boxed_2018_, v_b_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v_as_2008_);
lean_dec_ref(v_argVars_2007_);
lean_dec_ref(v_fst_2006_);
lean_dec_ref(v_a_2005_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
if (lean_obj_tag(v_a_2021_) == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_List_reverse___redArg(v_a_2022_);
return v___x_2023_;
}
else
{
lean_object* v_head_2024_; lean_object* v_tail_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2040_; 
v_head_2024_ = lean_ctor_get(v_a_2021_, 0);
v_tail_2025_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2027_ = v_a_2021_;
v_isShared_2028_ = v_isSharedCheck_2040_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_tail_2025_);
lean_inc(v_head_2024_);
lean_dec(v_a_2021_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2040_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; uint8_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2029_ = 0;
v___x_2030_ = lean_box(v___x_2029_);
v___x_2031_ = lean_array_get(v___x_2030_, v_fst_2020_, v_head_2024_);
lean_dec(v___x_2030_);
v___x_2032_ = 3;
v___x_2033_ = lean_unbox(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2034_ = l_Lean_instBEqBinderInfo_beq(v___x_2033_, v___x_2032_);
if (v___x_2034_ == 0)
{
lean_del_object(v___x_2027_);
lean_dec(v_head_2024_);
v_a_2021_ = v_tail_2025_;
goto _start;
}
else
{
lean_object* v___x_2037_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_a_2022_);
v___x_2037_ = v___x_2027_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_head_2024_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_a_2022_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_a_2021_ = v_tail_2025_;
v_a_2022_ = v___x_2037_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2041_, v_a_2042_, v_a_2043_);
lean_dec_ref(v_fst_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2045_, lean_object* v___x_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_b_2049_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_nat_dec_lt(v_a_2048_, v_upperBound_2045_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec(v_a_2048_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2049_);
return v___x_2052_;
}
else
{
lean_object* v_snd_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2094_; 
v_snd_2053_ = lean_ctor_get(v_b_2049_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_b_2049_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_b_2049_, 0);
lean_dec(v_unused_2095_);
v___x_2055_ = v_b_2049_;
v_isShared_2056_ = v_isSharedCheck_2094_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_snd_2053_);
lean_dec(v_b_2049_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2094_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_array_2057_; lean_object* v_start_2058_; lean_object* v_stop_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_array_2057_ = lean_ctor_get(v_snd_2053_, 0);
v_start_2058_ = lean_ctor_get(v_snd_2053_, 1);
v_stop_2059_ = lean_ctor_get(v_snd_2053_, 2);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_nat_dec_lt(v_start_2058_, v_stop_2059_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2063_; 
lean_dec(v_a_2048_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2060_);
v___x_2063_ = v___x_2055_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_snd_2053_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
else
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2090_; 
lean_inc(v_stop_2059_);
lean_inc(v_start_2058_);
lean_inc_ref(v_array_2057_);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_snd_2053_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2091_ = lean_ctor_get(v_snd_2053_, 2);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_snd_2053_, 1);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_snd_2053_, 0);
lean_dec(v_unused_2093_);
v___x_2067_ = v_snd_2053_;
v_isShared_2068_ = v_isSharedCheck_2090_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v_snd_2053_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2090_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_nat_dec_eq(v___x_2046_, v___x_2069_);
v___x_2071_ = lean_array_fget(v_array_2057_, v_start_2058_);
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_add(v_start_2058_, v___x_2072_);
lean_dec(v_start_2058_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2073_);
v___x_2075_ = v___x_2067_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_array_2057_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_stop_2059_);
v___x_2075_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
uint8_t v___x_2088_; 
v___x_2088_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2047_, v_a_2048_);
if (v___x_2088_ == 0)
{
goto v___jp_2082_;
}
else
{
if (v___x_2070_ == 0)
{
lean_dec(v___x_2071_);
goto v___jp_2076_;
}
else
{
goto v___jp_2082_;
}
}
v___jp_2076_:
{
lean_object* v___x_2078_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v___x_2075_);
lean_ctor_set(v___x_2055_, 0, v___x_2060_);
v___x_2078_ = v___x_2055_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2075_);
v___x_2078_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_nat_add(v_a_2048_, v___x_2072_);
lean_dec(v_a_2048_);
v_a_2048_ = v___x_2079_;
v_b_2049_ = v___x_2078_;
goto _start;
}
}
v___jp_2082_:
{
uint8_t v___x_2083_; 
v___x_2083_ = l_Lean_Expr_hasExprMVar(v___x_2071_);
lean_dec(v___x_2071_);
if (v___x_2083_ == 0)
{
goto v___jp_2076_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_del_object(v___x_2055_);
lean_dec(v_a_2048_);
v___x_2084_ = lean_box(v___x_2070_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2075_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2096_, lean_object* v___x_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2096_, v___x_2097_, v_a_2098_, v_a_2099_, v_b_2100_);
lean_dec_ref(v_a_2098_);
lean_dec(v___x_2097_);
lean_dec(v_upperBound_2096_);
return v_res_2102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2103_; lean_object* v_dummy_2104_; 
v___x_2103_ = lean_box(0);
v_dummy_2104_ = l_Lean_Expr_sort___override(v___x_2103_);
return v_dummy_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2105_, lean_object* v___x_2106_, uint8_t v___x_2107_, lean_object* v_x_2108_, lean_object* v_argTy_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
v___x_2115_ = lean_whnf(v_argTy_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2116_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_dummy_2119_; lean_object* v_nargs_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v_dummy_2119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2120_ = l_Lean_Expr_getAppNumArgs(v_a_2116_);
lean_inc(v_nargs_2120_);
v___x_2121_ = lean_mk_array(v_nargs_2120_, v_dummy_2119_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_sub(v_nargs_2120_, v___x_2122_);
lean_dec(v_nargs_2120_);
v___x_2124_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2116_, v___x_2121_, v___x_2123_);
v___x_2125_ = lean_array_get_size(v___x_2124_);
lean_inc(v___x_2105_);
v___x_2126_ = l_Array_toSubarray___redArg(v___x_2124_, v___x_2105_, v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
v___x_2129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2125_, v___x_2106_, v_a_2118_, v___x_2105_, v___x_2128_);
lean_dec(v_a_2118_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2143_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_fst_2134_; 
v_fst_2134_ = lean_ctor_get(v_a_2130_, 0);
lean_inc(v_fst_2134_);
lean_dec(v_a_2130_);
if (lean_obj_tag(v_fst_2134_) == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(v___x_2107_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2135_);
v___x_2137_ = v___x_2132_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2141_; 
v_val_2139_ = lean_ctor_get(v_fst_2134_, 0);
lean_inc(v_val_2139_);
lean_dec_ref(v_fst_2134_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v_val_2139_);
v___x_2141_ = v___x_2132_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_val_2139_);
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
v_a_2144_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2129_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2129_);
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
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2116_);
lean_dec(v___x_2105_);
v_a_2152_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2117_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2117_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v___x_2105_);
v_a_2160_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2115_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2115_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2168_, lean_object* v___x_2169_, lean_object* v___x_2170_, lean_object* v_x_2171_, lean_object* v_argTy_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_24484__boxed_2178_; lean_object* v_res_2179_; 
v___x_24484__boxed_2178_ = lean_unbox(v___x_2170_);
v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2168_, v___x_2169_, v___x_24484__boxed_2178_, v_x_2171_, v_argTy_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_x_2171_);
lean_dec(v___x_2169_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2183_, lean_object* v_projInfo_x3f_2184_, lean_object* v___x_2185_, lean_object* v_argVars_2186_, lean_object* v_as_2187_, size_t v_sz_2188_, size_t v_i_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = lean_usize_dec_lt(v_i_2189_, v_sz_2188_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
lean_dec(v___x_2185_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_b_2190_);
return v___x_2197_;
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec_ref(v_b_2190_);
v_a_2198_ = lean_array_uget_borrowed(v_as_2187_, v_i_2189_);
v___x_2199_ = l_Lean_instInhabitedExpr;
v___x_2200_ = lean_array_get_borrowed(v___x_2199_, v_fst_2183_, v_a_2198_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___x_2200_);
v___x_2201_ = lean_infer_type(v___x_2200_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2202_, v___y_2192_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2250_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2250_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2250_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2216_; lean_object* v___y_2218_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; uint8_t v___x_2235_; 
v___x_2208_ = lean_box(0);
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_box(v___x_2196_);
lean_inc(v___x_2185_);
v___f_2234_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2234_, 0, v___x_2232_);
lean_closure_set(v___f_2234_, 1, v___x_2185_);
lean_closure_set(v___f_2234_, 2, v___x_2233_);
v___x_2235_ = lean_nat_dec_eq(v___x_2185_, v___x_2232_);
if (lean_obj_tag(v_projInfo_x3f_2184_) == 1)
{
lean_object* v_val_2236_; lean_object* v_numParams_2237_; uint8_t v___x_2238_; 
v_val_2236_ = lean_ctor_get(v_projInfo_x3f_2184_, 0);
v_numParams_2237_ = lean_ctor_get(v_val_2236_, 1);
v___x_2238_ = lean_nat_dec_eq(v_numParams_2237_, v_a_2198_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2204_, v___f_2234_, v___x_2235_, v___x_2235_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v___y_2218_ = v___x_2239_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2240_; 
lean_dec_ref(v___f_2234_);
lean_dec(v___x_2185_);
v___x_2240_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2183_, v_argVars_2186_, v_a_2204_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_dec_ref(v___x_2240_);
goto v___jp_2209_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2206_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2204_, v___f_2234_, v___x_2235_, v___x_2235_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v___y_2218_ = v___x_2249_;
goto v___jp_2217_;
}
v___jp_2209_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_inc(v_a_2198_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2198_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2208_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2212_);
v___x_2214_ = v___x_2206_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
v___jp_2217_:
{
if (lean_obj_tag(v___y_2218_) == 0)
{
lean_object* v_a_2219_; uint8_t v___x_2220_; 
v_a_2219_ = lean_ctor_get(v___y_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref(v___y_2218_);
v___x_2220_ = lean_unbox(v_a_2219_);
lean_dec(v_a_2219_);
if (v___x_2220_ == 0)
{
size_t v___x_2221_; size_t v___x_2222_; 
lean_del_object(v___x_2206_);
v___x_2221_ = ((size_t)1ULL);
v___x_2222_ = lean_usize_add(v_i_2189_, v___x_2221_);
v_i_2189_ = v___x_2222_;
v_b_2190_ = v___x_2216_;
goto _start;
}
else
{
lean_dec(v___x_2185_);
goto v___jp_2209_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_del_object(v___x_2206_);
lean_dec(v___x_2185_);
v_a_2224_ = lean_ctor_get(v___y_2218_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___y_2218_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___y_2218_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___y_2218_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v___x_2185_);
v_a_2251_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2203_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2203_);
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
lean_dec(v___x_2185_);
v_a_2259_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2201_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2201_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2267_, lean_object* v_projInfo_x3f_2268_, lean_object* v___x_2269_, lean_object* v_argVars_2270_, lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
size_t v_sz_boxed_2280_; size_t v_i_boxed_2281_; lean_object* v_res_2282_; 
v_sz_boxed_2280_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2281_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2267_, v_projInfo_x3f_2268_, v___x_2269_, v_argVars_2270_, v_as_2271_, v_sz_boxed_2280_, v_i_boxed_2281_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v_as_2271_);
lean_dec_ref(v_argVars_2270_);
lean_dec(v_projInfo_x3f_2268_);
lean_dec_ref(v_fst_2267_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_env_2290_; lean_object* v___x_2291_; lean_object* v_mctx_2292_; lean_object* v_lctx_2293_; lean_object* v_options_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2289_ = lean_st_ref_get(v___y_2287_);
v_env_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc_ref(v_env_2290_);
lean_dec(v___x_2289_);
v___x_2291_ = lean_st_ref_get(v___y_2285_);
v_mctx_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_ref(v_mctx_2292_);
lean_dec(v___x_2291_);
v_lctx_2293_ = lean_ctor_get(v___y_2284_, 2);
v_options_2294_ = lean_ctor_get(v___y_2286_, 2);
lean_inc_ref(v_options_2294_);
lean_inc_ref(v_lctx_2293_);
v___x_2295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2295_, 0, v_env_2290_);
lean_ctor_set(v___x_2295_, 1, v_mctx_2292_);
lean_ctor_set(v___x_2295_, 2, v_lctx_2293_);
lean_ctor_set(v___x_2295_, 3, v_options_2294_);
v___x_2296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v_msgData_2283_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_ref_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_ref_2311_ = lean_ctor_get(v___y_2308_, 5);
v___x_2312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_inc(v_ref_2311_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_ref_2311_);
lean_ctor_set(v___x_2317_, 1, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set_tag(v___x_2315_, 1);
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2329_, lean_object* v_as_2330_, size_t v_i_2331_, size_t v_stop_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v___y_2335_; uint8_t v___x_2339_; 
v___x_2339_ = lean_usize_dec_eq(v_i_2331_, v_stop_2332_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_array_uget_borrowed(v_as_2330_, v_i_2331_);
v___x_2341_ = lean_nat_dec_eq(v___x_2340_, v_next_2329_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_inc(v___x_2340_);
v___x_2342_ = lean_array_push(v_b_2333_, v___x_2340_);
v___y_2335_ = v___x_2342_;
goto v___jp_2334_;
}
else
{
v___y_2335_ = v_b_2333_;
goto v___jp_2334_;
}
}
else
{
return v_b_2333_;
}
v___jp_2334_:
{
size_t v___x_2336_; size_t v___x_2337_; 
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2331_, v___x_2336_);
v_i_2331_ = v___x_2337_;
v_b_2333_ = v___y_2335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2343_, lean_object* v_as_2344_, lean_object* v_i_2345_, lean_object* v_stop_2346_, lean_object* v_b_2347_){
_start:
{
size_t v_i_boxed_2348_; size_t v_stop_boxed_2349_; lean_object* v_res_2350_; 
v_i_boxed_2348_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_stop_boxed_2349_ = lean_unbox_usize(v_stop_2346_);
lean_dec(v_stop_2346_);
v_res_2350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2343_, v_as_2344_, v_i_boxed_2348_, v_stop_boxed_2349_, v_b_2347_);
lean_dec_ref(v_as_2344_);
lean_dec(v_next_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2351_, size_t v_sz_2352_, size_t v_i_2353_, lean_object* v_bs_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2353_, v_sz_2352_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_bs_2354_);
return v___x_2361_;
}
else
{
lean_object* v_v_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_v_2362_ = lean_array_uget_borrowed(v_bs_2354_, v_i_2353_);
v___x_2363_ = l_Lean_instInhabitedExpr;
v___x_2364_ = lean_array_get_borrowed(v___x_2363_, v_fst_2351_, v_v_2362_);
lean_inc(v___y_2358_);
lean_inc_ref(v___y_2357_);
lean_inc(v___y_2356_);
lean_inc_ref(v___y_2355_);
lean_inc(v___x_2364_);
v___x_2365_ = lean_infer_type(v___x_2364_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2366_, v___y_2356_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v_bs_x27_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = lean_unsigned_to_nat(0u);
v_bs_x27_2370_ = lean_array_uset(v_bs_2354_, v_i_2353_, v___x_2369_);
v___x_2371_ = l_Lean_Expr_setPPExplicit(v_a_2368_, v___x_2360_);
v___x_2372_ = l_Lean_indentExpr(v___x_2371_);
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_add(v_i_2353_, v___x_2373_);
v___x_2375_ = lean_array_uset(v_bs_x27_2370_, v_i_2353_, v___x_2372_);
v_i_2353_ = v___x_2374_;
v_bs_2354_ = v___x_2375_;
goto _start;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec_ref(v_bs_2354_);
v_a_2377_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2367_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2367_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v_bs_2354_);
v_a_2385_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2365_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2365_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2393_, lean_object* v_sz_2394_, lean_object* v_i_2395_, lean_object* v_bs_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
size_t v_sz_boxed_2402_; size_t v_i_boxed_2403_; lean_object* v_res_2404_; 
v_sz_boxed_2402_ = lean_unbox_usize(v_sz_2394_);
lean_dec(v_sz_2394_);
v_i_boxed_2403_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2393_, v_sz_boxed_2402_, v_i_boxed_2403_, v_bs_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v_fst_2393_);
return v_res_2404_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2409_ = l_Lean_MessageData_ofFormat(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2419_, lean_object* v_argVars_2420_, lean_object* v_inst_2421_, lean_object* v_a_2422_, lean_object* v_projInfo_x3f_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v_fst_2470_; lean_object* v_snd_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2561_; 
v_fst_2470_ = lean_ctor_get(v_b_2424_, 0);
v_snd_2471_ = lean_ctor_get(v_b_2424_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_b_2424_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2473_ = v_b_2424_;
v_isShared_2474_ = v_isSharedCheck_2561_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_snd_2471_);
lean_inc(v_fst_2470_);
lean_dec(v_b_2424_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2561_;
goto v_resetjp_2472_;
}
v___jp_2430_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_instInhabitedExpr;
v___x_2439_ = lean_array_get_borrowed(v___x_2438_, v_fst_2419_, v___y_2436_);
lean_dec(v___y_2436_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2434_);
lean_inc(v___x_2439_);
v___x_2440_ = lean_infer_type(v___x_2439_, v___y_2434_, v___y_2432_, v___y_2431_, v___y_2433_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2419_, v_argVars_2420_, v_a_2441_, v___y_2434_, v___y_2432_, v___y_2431_, v___y_2433_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v___x_2442_);
lean_inc(v___x_2439_);
v___x_2443_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2419_, v_argVars_2420_, v___x_2439_, v___y_2434_, v___y_2432_, v___y_2431_, v___y_2433_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref(v___x_2443_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2435_);
lean_ctor_set(v___x_2444_, 1, v___y_2437_);
v_b_2424_ = v___x_2444_;
goto _start;
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2446_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2443_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2443_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2454_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2442_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2442_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2462_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2440_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2440_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
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
v_resetjp_2472_:
{
lean_object* v_next_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_array_get_size(v_snd_2471_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = lean_nat_dec_eq(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; size_t v_sz_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
lean_del_object(v___x_2473_);
v___x_2541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2542_ = lean_array_size(v_snd_2471_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2419_, v_projInfo_x3f_2423_, v___x_2538_, v_argVars_2420_, v_snd_2471_, v_sz_2542_, v___x_2543_, v___x_2541_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_fst_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v_fst_2546_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_fst_2546_);
lean_dec(v_a_2545_);
if (lean_obj_tag(v_fst_2546_) == 0)
{
goto v___jp_2500_;
}
else
{
lean_object* v_val_2547_; 
v_val_2547_ = lean_ctor_get(v_fst_2546_, 0);
lean_inc(v_val_2547_);
lean_dec_ref(v_fst_2546_);
if (lean_obj_tag(v_val_2547_) == 0)
{
goto v___jp_2500_;
}
else
{
lean_object* v_val_2548_; 
v_val_2548_ = lean_ctor_get(v_val_2547_, 0);
lean_inc(v_val_2548_);
lean_dec_ref(v_val_2547_);
v_next_2476_ = v_val_2548_;
v___y_2477_ = v___y_2425_;
v___y_2478_ = v___y_2426_;
v___y_2479_ = v___y_2427_;
v___y_2480_ = v___y_2428_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_snd_2471_);
lean_dec(v_fst_2470_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2549_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2544_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2544_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v___x_2558_; 
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
if (v_isShared_2474_ == 0)
{
v___x_2558_ = v___x_2473_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_fst_2470_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_snd_2471_);
v___x_2558_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
v___jp_2475_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
lean_inc(v_next_2476_);
v___x_2481_ = lean_array_push(v_fst_2470_, v_next_2476_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_array_get_size(v_snd_2471_);
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2485_ = lean_nat_dec_lt(v___x_2482_, v___x_2483_);
if (v___x_2485_ == 0)
{
lean_dec(v_snd_2471_);
v___y_2431_ = v___y_2479_;
v___y_2432_ = v___y_2478_;
v___y_2433_ = v___y_2480_;
v___y_2434_ = v___y_2477_;
v___y_2435_ = v___x_2481_;
v___y_2436_ = v_next_2476_;
v___y_2437_ = v___x_2484_;
goto v___jp_2430_;
}
else
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_nat_dec_le(v___x_2483_, v___x_2483_);
if (v___x_2486_ == 0)
{
if (v___x_2485_ == 0)
{
lean_dec(v_snd_2471_);
v___y_2431_ = v___y_2479_;
v___y_2432_ = v___y_2478_;
v___y_2433_ = v___y_2480_;
v___y_2434_ = v___y_2477_;
v___y_2435_ = v___x_2481_;
v___y_2436_ = v_next_2476_;
v___y_2437_ = v___x_2484_;
goto v___jp_2430_;
}
else
{
size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = lean_usize_of_nat(v___x_2483_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2476_, v_snd_2471_, v___x_2487_, v___x_2488_, v___x_2484_);
lean_dec(v_snd_2471_);
v___y_2431_ = v___y_2479_;
v___y_2432_ = v___y_2478_;
v___y_2433_ = v___y_2480_;
v___y_2434_ = v___y_2477_;
v___y_2435_ = v___x_2481_;
v___y_2436_ = v_next_2476_;
v___y_2437_ = v___x_2489_;
goto v___jp_2430_;
}
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2483_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2476_, v_snd_2471_, v___x_2490_, v___x_2491_, v___x_2484_);
lean_dec(v_snd_2471_);
v___y_2431_ = v___y_2479_;
v___y_2432_ = v___y_2478_;
v___y_2433_ = v___y_2480_;
v___y_2434_ = v___y_2477_;
v___y_2435_ = v___x_2481_;
v___y_2436_ = v_next_2476_;
v___y_2437_ = v___x_2492_;
goto v___jp_2430_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = lean_array_get_borrowed(v___x_2498_, v_snd_2471_, v___x_2498_);
lean_inc(v___x_2499_);
v_next_2476_ = v___x_2499_;
v___y_2477_ = v___y_2494_;
v___y_2478_ = v___y_2495_;
v___y_2479_ = v___y_2496_;
v___y_2480_ = v___y_2497_;
goto v___jp_2475_;
}
v___jp_2500_:
{
lean_object* v_options_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_options_2501_ = lean_ctor_get(v___y_2427_, 2);
v___x_2502_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2503_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
v___y_2494_ = v___y_2425_;
v___y_2495_ = v___y_2426_;
v___y_2496_ = v___y_2427_;
v___y_2497_ = v___y_2428_;
goto v___jp_2493_;
}
else
{
size_t v_sz_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v_sz_2504_ = lean_array_size(v_snd_2471_);
v___x_2505_ = ((size_t)0ULL);
lean_inc(v_snd_2471_);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2419_, v_sz_2504_, v___x_2505_, v_snd_2471_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = lean_array_to_list(v_a_2507_);
v___x_2509_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2510_ = l_Lean_MessageData_joinSep(v___x_2508_, v___x_2509_);
v___x_2511_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2421_);
v___x_2512_ = l_Lean_MessageData_ofExpr(v_inst_2421_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_inc_ref(v_a_2422_);
v___x_2516_ = l_Lean_indentExpr(v_a_2422_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2510_);
v___x_2521_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2520_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_dec_ref(v___x_2521_);
v___y_2494_ = v___y_2425_;
v___y_2495_ = v___y_2426_;
v___y_2496_ = v___y_2427_;
v___y_2497_ = v___y_2428_;
goto v___jp_2493_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_snd_2471_);
lean_dec(v_fst_2470_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_snd_2471_);
lean_dec(v_fst_2470_);
lean_dec_ref(v_a_2422_);
lean_dec_ref(v_inst_2421_);
v_a_2530_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2506_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2506_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2562_, lean_object* v_argVars_2563_, lean_object* v_inst_2564_, lean_object* v_a_2565_, lean_object* v_projInfo_x3f_2566_, lean_object* v_b_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2562_, v_argVars_2563_, v_inst_2564_, v_a_2565_, v_projInfo_x3f_2566_, v_b_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v_projInfo_x3f_2566_);
lean_dec_ref(v_argVars_2563_);
lean_dec_ref(v_fst_2562_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2574_, size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_bs_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_lt(v_i_2576_, v_sz_2575_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_bs_2577_);
return v___x_2584_;
}
else
{
lean_object* v_v_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_v_2585_ = lean_array_uget_borrowed(v_bs_2577_, v_i_2576_);
v___x_2586_ = l_Lean_instInhabitedExpr;
v___x_2587_ = lean_array_get_borrowed(v___x_2586_, v_argVars_2574_, v_v_2585_);
lean_inc(v___y_2581_);
lean_inc_ref(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
lean_inc(v___x_2587_);
v___x_2588_ = lean_infer_type(v___x_2587_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v_bs_x27_2591_; lean_object* v___x_2592_; size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v_bs_x27_2591_ = lean_array_uset(v_bs_2577_, v_i_2576_, v___x_2590_);
v___x_2592_ = l_Lean_indentExpr(v_a_2589_);
v___x_2593_ = ((size_t)1ULL);
v___x_2594_ = lean_usize_add(v_i_2576_, v___x_2593_);
v___x_2595_ = lean_array_uset(v_bs_x27_2591_, v_i_2576_, v___x_2592_);
v_i_2576_ = v___x_2594_;
v_bs_2577_ = v___x_2595_;
goto _start;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v_bs_2577_);
v_a_2597_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2588_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2588_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2605_, lean_object* v_sz_2606_, lean_object* v_i_2607_, lean_object* v_bs_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
size_t v_sz_boxed_2614_; size_t v_i_boxed_2615_; lean_object* v_res_2616_; 
v_sz_boxed_2614_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2615_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2605_, v_sz_boxed_2614_, v_i_boxed_2615_, v_bs_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v_argVars_2605_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
if (lean_obj_tag(v_a_2617_) == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = l_List_reverse___redArg(v_a_2618_);
return v___x_2619_;
}
else
{
lean_object* v_head_2620_; lean_object* v_tail_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2632_; 
v_head_2620_ = lean_ctor_get(v_a_2617_, 0);
v_tail_2621_ = lean_ctor_get(v_a_2617_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2623_ = v_a_2617_;
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_tail_2621_);
lean_inc(v_head_2620_);
lean_dec(v_a_2617_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2625_ = l_Nat_reprFast(v_head_2620_);
v___x_2626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = l_Lean_MessageData_ofFormat(v___x_2626_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v_a_2618_);
lean_ctor_set(v___x_2623_, 0, v___x_2627_);
v___x_2629_ = v___x_2623_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_a_2618_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
v_a_2617_ = v_tail_2621_;
v_a_2618_ = v___x_2629_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2633_; double v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_float_of_nat(v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2637_, lean_object* v_msg_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_ref_2644_; lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2690_; 
v_ref_2644_ = lean_ctor_get(v___y_2641_, 5);
v___x_2645_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2690_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2690_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v_traceState_2651_; lean_object* v_env_2652_; lean_object* v_nextMacroScope_2653_; lean_object* v_ngen_2654_; lean_object* v_auxDeclNGen_2655_; lean_object* v_cache_2656_; lean_object* v_messages_2657_; lean_object* v_infoState_2658_; lean_object* v_snapshotTasks_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2689_; 
v___x_2650_ = lean_st_ref_take(v___y_2642_);
v_traceState_2651_ = lean_ctor_get(v___x_2650_, 4);
v_env_2652_ = lean_ctor_get(v___x_2650_, 0);
v_nextMacroScope_2653_ = lean_ctor_get(v___x_2650_, 1);
v_ngen_2654_ = lean_ctor_get(v___x_2650_, 2);
v_auxDeclNGen_2655_ = lean_ctor_get(v___x_2650_, 3);
v_cache_2656_ = lean_ctor_get(v___x_2650_, 5);
v_messages_2657_ = lean_ctor_get(v___x_2650_, 6);
v_infoState_2658_ = lean_ctor_get(v___x_2650_, 7);
v_snapshotTasks_2659_ = lean_ctor_get(v___x_2650_, 8);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2661_ = v___x_2650_;
v_isShared_2662_ = v_isSharedCheck_2689_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snapshotTasks_2659_);
lean_inc(v_infoState_2658_);
lean_inc(v_messages_2657_);
lean_inc(v_cache_2656_);
lean_inc(v_traceState_2651_);
lean_inc(v_auxDeclNGen_2655_);
lean_inc(v_ngen_2654_);
lean_inc(v_nextMacroScope_2653_);
lean_inc(v_env_2652_);
lean_dec(v___x_2650_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2689_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint64_t v_tid_2663_; lean_object* v_traces_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2688_; 
v_tid_2663_ = lean_ctor_get_uint64(v_traceState_2651_, sizeof(void*)*1);
v_traces_2664_ = lean_ctor_get(v_traceState_2651_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_traceState_2651_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2666_ = v_traceState_2651_;
v_isShared_2667_ = v_isSharedCheck_2688_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_traces_2664_);
lean_dec(v_traceState_2651_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2688_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; double v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2670_ = 0;
v___x_2671_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2672_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2672_, 0, v_cls_2637_);
lean_ctor_set(v___x_2672_, 1, v___x_2668_);
lean_ctor_set(v___x_2672_, 2, v___x_2671_);
lean_ctor_set_float(v___x_2672_, sizeof(void*)*3, v___x_2669_);
lean_ctor_set_float(v___x_2672_, sizeof(void*)*3 + 8, v___x_2669_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*3 + 16, v___x_2670_);
v___x_2673_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2674_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v_a_2646_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
lean_inc(v_ref_2644_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_ref_2644_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_PersistentArray_push___redArg(v_traces_2664_, v___x_2675_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2676_);
v___x_2678_ = v___x_2666_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2676_);
lean_ctor_set_uint64(v_reuseFailAlloc_2687_, sizeof(void*)*1, v_tid_2663_);
v___x_2678_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 4, v___x_2678_);
v___x_2680_ = v___x_2661_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_env_2652_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_nextMacroScope_2653_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_ngen_2654_);
lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_auxDeclNGen_2655_);
lean_ctor_set(v_reuseFailAlloc_2686_, 4, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2686_, 5, v_cache_2656_);
lean_ctor_set(v_reuseFailAlloc_2686_, 6, v_messages_2657_);
lean_ctor_set(v_reuseFailAlloc_2686_, 7, v_infoState_2658_);
lean_ctor_set(v_reuseFailAlloc_2686_, 8, v_snapshotTasks_2659_);
v___x_2680_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = lean_st_ref_set(v___y_2642_, v___x_2680_);
v___x_2682_ = lean_box(0);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2682_);
v___x_2684_ = v___x_2648_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2691_, lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2691_, v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2708_ = l_Lean_Name_append(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2721_, lean_object* v_fst_2722_, lean_object* v_fst_2723_, lean_object* v_inst_2724_, lean_object* v_a_2725_, lean_object* v_projInfo_x3f_2726_, lean_object* v_argVars_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2721_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v_dummy_2736_; lean_object* v_nargs_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; size_t v_sz_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
v_dummy_2736_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2737_ = l_Lean_Expr_getAppNumArgs(v_a_2721_);
lean_inc(v_nargs_2737_);
v___x_2738_ = lean_mk_array(v_nargs_2737_, v_dummy_2736_);
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_sub(v_nargs_2737_, v___x_2739_);
lean_dec(v_nargs_2737_);
lean_inc_ref(v_a_2721_);
v___x_2741_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2721_, v___x_2738_, v___x_2740_);
v___x_2742_ = lean_array_get_size(v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___x_2742_);
v_sz_2745_ = lean_array_size(v___x_2741_);
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2735_, v_fst_2722_, v_argVars_2727_, v___x_2741_, v_sz_2745_, v___x_2746_, v___x_2744_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v___x_2741_);
lean_dec(v_a_2735_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec_ref(v___x_2747_);
v___x_2748_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2749_ = lean_array_get_size(v_fst_2722_);
v___x_2750_ = l_List_range(v___x_2749_);
v___x_2751_ = lean_box(0);
v___x_2752_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2723_, v___x_2750_, v___x_2751_);
v___x_2753_ = lean_array_mk(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2748_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_inc_ref(v_inst_2724_);
v___x_2755_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2722_, v_argVars_2727_, v_inst_2724_, v_a_2725_, v_projInfo_x3f_2726_, v___x_2754_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2848_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2848_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2848_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_fst_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2846_; 
v_fst_2760_ = lean_ctor_get(v_a_2756_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_a_2756_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v_a_2756_, 1);
lean_dec(v_unused_2847_);
v___x_2762_ = v_a_2756_;
v_isShared_2763_ = v_isSharedCheck_2846_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_fst_2760_);
lean_dec(v_a_2756_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2846_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v_options_2768_; lean_object* v_inheritedTraceOptions_2769_; lean_object* v___y_2770_; lean_object* v_options_2826_; lean_object* v_inheritedTraceOptions_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v_options_2826_ = lean_ctor_get(v___y_2731_, 2);
v_inheritedTraceOptions_2827_ = lean_ctor_get(v___y_2731_, 13);
v___x_2828_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2829_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2826_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_dec_ref(v_a_2721_);
v___y_2765_ = v___y_2729_;
v___y_2766_ = v___y_2730_;
v___y_2767_ = v___y_2731_;
v_options_2768_ = v_options_2826_;
v_inheritedTraceOptions_2769_ = v_inheritedTraceOptions_2827_;
v___y_2770_ = v___y_2732_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2830_; lean_object* v_a_2831_; uint8_t v___x_2832_; 
v___x_2830_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2721_, v___y_2730_);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = l_Lean_Expr_hasExprMVar(v_a_2831_);
if (v___x_2832_ == 0)
{
lean_dec(v_a_2831_);
v___y_2765_ = v___y_2729_;
v___y_2766_ = v___y_2730_;
v___y_2767_ = v___y_2731_;
v_options_2768_ = v_options_2826_;
v_inheritedTraceOptions_2769_ = v_inheritedTraceOptions_2827_;
v___y_2770_ = v___y_2732_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_del_object(v___x_2762_);
lean_dec(v_fst_2760_);
lean_del_object(v___x_2758_);
lean_dec_ref(v_inst_2724_);
v___x_2833_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2834_ = l_Lean_Expr_setPPExplicit(v_a_2831_, v___x_2832_);
v___x_2835_ = l_Lean_indentExpr(v___x_2834_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2833_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2836_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
v___jp_2764_:
{
uint8_t v_hasTrace_2771_; 
v_hasTrace_2771_ = lean_ctor_get_uint8(v_options_2768_, sizeof(void*)*1);
if (v_hasTrace_2771_ == 0)
{
lean_object* v___x_2773_; 
lean_del_object(v___x_2762_);
lean_dec_ref(v_inst_2724_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_fst_2760_);
v___x_2773_ = v___x_2758_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_fst_2760_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2776_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2769_, v_options_2768_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2779_; 
lean_del_object(v___x_2762_);
lean_dec_ref(v_inst_2724_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_fst_2760_);
v___x_2779_ = v___x_2758_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_fst_2760_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
size_t v_sz_2781_; lean_object* v___x_2782_; 
lean_del_object(v___x_2758_);
v_sz_2781_ = lean_array_size(v_fst_2760_);
lean_inc(v_fst_2760_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2727_, v_sz_2781_, v___x_2746_, v_fst_2760_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2770_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2785_ = l_Lean_MessageData_ofExpr(v_inst_2724_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 7);
lean_ctor_set(v___x_2762_, 1, v___x_2785_);
lean_ctor_set(v___x_2762_, 0, v___x_2784_);
v___x_2787_ = v___x_2762_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
lean_inc(v_fst_2760_);
v___x_2790_ = lean_array_to_list(v_fst_2760_);
v___x_2791_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2790_, v___x_2751_);
v___x_2792_ = l_Lean_MessageData_ofList(v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2789_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_array_to_list(v_a_2783_);
v___x_2797_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2798_ = l_Lean_MessageData_joinSep(v___x_2796_, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2795_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2775_, v___x_2799_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2770_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2800_, 0);
lean_dec(v_unused_2808_);
v___x_2802_ = v___x_2800_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v___x_2800_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_fst_2760_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_fst_2760_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_fst_2760_);
v_a_2809_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2800_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2800_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2762_);
lean_dec(v_fst_2760_);
lean_dec_ref(v_inst_2724_);
v_a_2818_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2782_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2782_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
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
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v_inst_2724_);
lean_dec_ref(v_a_2721_);
v_a_2849_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2755_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2755_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_a_2725_);
lean_dec_ref(v_inst_2724_);
lean_dec_ref(v_a_2721_);
v_a_2857_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2747_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2747_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_dec_ref(v_a_2725_);
lean_dec_ref(v_inst_2724_);
lean_dec_ref(v_a_2721_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2865_, lean_object* v_fst_2866_, lean_object* v_fst_2867_, lean_object* v_inst_2868_, lean_object* v_a_2869_, lean_object* v_projInfo_x3f_2870_, lean_object* v_argVars_2871_, lean_object* v_x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2865_, v_fst_2866_, v_fst_2867_, v_inst_2868_, v_a_2869_, v_projInfo_x3f_2870_, v_argVars_2871_, v_x_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_x_2872_);
lean_dec_ref(v_argVars_2871_);
lean_dec(v_projInfo_x3f_2870_);
lean_dec_ref(v_fst_2867_);
lean_dec_ref(v_fst_2866_);
return v_res_2878_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2879_; uint64_t v___x_2880_; 
v___x_2879_ = 2;
v___x_2880_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2881_, lean_object* v_projInfo_x3f_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2888_; uint8_t v_foApprox_2889_; uint8_t v_ctxApprox_2890_; uint8_t v_quasiPatternApprox_2891_; uint8_t v_constApprox_2892_; uint8_t v_isDefEqStuckEx_2893_; uint8_t v_unificationHints_2894_; uint8_t v_proofIrrelevance_2895_; uint8_t v_assignSyntheticOpaque_2896_; uint8_t v_offsetCnstrs_2897_; uint8_t v_etaStruct_2898_; uint8_t v_univApprox_2899_; uint8_t v_iota_2900_; uint8_t v_beta_2901_; uint8_t v_proj_2902_; uint8_t v_zeta_2903_; uint8_t v_zetaDelta_2904_; uint8_t v_zetaUnused_2905_; uint8_t v_zetaHave_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2971_; 
v___x_2888_ = l_Lean_Meta_Context_config(v_a_2883_);
v_foApprox_2889_ = lean_ctor_get_uint8(v___x_2888_, 0);
v_ctxApprox_2890_ = lean_ctor_get_uint8(v___x_2888_, 1);
v_quasiPatternApprox_2891_ = lean_ctor_get_uint8(v___x_2888_, 2);
v_constApprox_2892_ = lean_ctor_get_uint8(v___x_2888_, 3);
v_isDefEqStuckEx_2893_ = lean_ctor_get_uint8(v___x_2888_, 4);
v_unificationHints_2894_ = lean_ctor_get_uint8(v___x_2888_, 5);
v_proofIrrelevance_2895_ = lean_ctor_get_uint8(v___x_2888_, 6);
v_assignSyntheticOpaque_2896_ = lean_ctor_get_uint8(v___x_2888_, 7);
v_offsetCnstrs_2897_ = lean_ctor_get_uint8(v___x_2888_, 8);
v_etaStruct_2898_ = lean_ctor_get_uint8(v___x_2888_, 10);
v_univApprox_2899_ = lean_ctor_get_uint8(v___x_2888_, 11);
v_iota_2900_ = lean_ctor_get_uint8(v___x_2888_, 12);
v_beta_2901_ = lean_ctor_get_uint8(v___x_2888_, 13);
v_proj_2902_ = lean_ctor_get_uint8(v___x_2888_, 14);
v_zeta_2903_ = lean_ctor_get_uint8(v___x_2888_, 15);
v_zetaDelta_2904_ = lean_ctor_get_uint8(v___x_2888_, 16);
v_zetaUnused_2905_ = lean_ctor_get_uint8(v___x_2888_, 17);
v_zetaHave_2906_ = lean_ctor_get_uint8(v___x_2888_, 18);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2908_ = v___x_2888_;
v_isShared_2909_ = v_isSharedCheck_2971_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v___x_2888_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2971_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
uint8_t v_trackZetaDelta_2910_; lean_object* v_zetaDeltaSet_2911_; lean_object* v_lctx_2912_; lean_object* v_localInstances_2913_; lean_object* v_defEqCtx_x3f_2914_; lean_object* v_synthPendingDepth_2915_; lean_object* v_canUnfold_x3f_2916_; uint8_t v_univApprox_2917_; uint8_t v_inTypeClassResolution_2918_; uint8_t v_cacheInferType_2919_; uint8_t v___x_2920_; lean_object* v_config_2922_; 
v_trackZetaDelta_2910_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*7);
v_zetaDeltaSet_2911_ = lean_ctor_get(v_a_2883_, 1);
v_lctx_2912_ = lean_ctor_get(v_a_2883_, 2);
v_localInstances_2913_ = lean_ctor_get(v_a_2883_, 3);
v_defEqCtx_x3f_2914_ = lean_ctor_get(v_a_2883_, 4);
v_synthPendingDepth_2915_ = lean_ctor_get(v_a_2883_, 5);
v_canUnfold_x3f_2916_ = lean_ctor_get(v_a_2883_, 6);
v_univApprox_2917_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2918_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*7 + 2);
v_cacheInferType_2919_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*7 + 3);
v___x_2920_ = 2;
if (v_isShared_2909_ == 0)
{
v_config_2922_ = v___x_2908_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 0, v_foApprox_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 1, v_ctxApprox_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 2, v_quasiPatternApprox_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 3, v_constApprox_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 4, v_isDefEqStuckEx_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 5, v_unificationHints_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 6, v_proofIrrelevance_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 7, v_assignSyntheticOpaque_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 8, v_offsetCnstrs_2897_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 10, v_etaStruct_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 11, v_univApprox_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 12, v_iota_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 13, v_beta_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 14, v_proj_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 15, v_zeta_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 16, v_zetaDelta_2904_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 17, v_zetaUnused_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, 18, v_zetaHave_2906_);
v_config_2922_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; uint64_t v_key_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_ctor_set_uint8(v_config_2922_, 9, v___x_2920_);
v___x_2923_ = l_Lean_Meta_Context_configKey(v_a_2883_);
v___x_2924_ = 2ULL;
v___x_2925_ = lean_uint64_shift_right(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_uint64_shift_left(v___x_2925_, v___x_2924_);
v___x_2927_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2928_ = lean_uint64_lor(v___x_2926_, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2929_, 0, v_config_2922_);
lean_ctor_set_uint64(v___x_2929_, sizeof(void*)*1, v_key_2928_);
lean_inc(v_canUnfold_x3f_2916_);
lean_inc(v_synthPendingDepth_2915_);
lean_inc(v_defEqCtx_x3f_2914_);
lean_inc_ref(v_localInstances_2913_);
lean_inc_ref(v_lctx_2912_);
lean_inc(v_zetaDeltaSet_2911_);
v___x_2930_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_zetaDeltaSet_2911_);
lean_ctor_set(v___x_2930_, 2, v_lctx_2912_);
lean_ctor_set(v___x_2930_, 3, v_localInstances_2913_);
lean_ctor_set(v___x_2930_, 4, v_defEqCtx_x3f_2914_);
lean_ctor_set(v___x_2930_, 5, v_synthPendingDepth_2915_);
lean_ctor_set(v___x_2930_, 6, v_canUnfold_x3f_2916_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*7, v_trackZetaDelta_2910_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*7 + 1, v_univApprox_2917_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2918_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*7 + 3, v_cacheInferType_2919_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v___x_2930_);
lean_inc_ref(v_inst_2881_);
v___x_2931_ = lean_infer_type(v_inst_2881_, v___x_2930_, v_a_2884_, v_a_2885_, v_a_2886_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_n(v_a_2932_, 2);
lean_dec_ref(v___x_2931_);
v___x_2933_ = lean_box(0);
v___x_2934_ = 0;
v___x_2935_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2932_, v___x_2933_, v___x_2934_, v___x_2930_, v_a_2884_, v_a_2885_, v_a_2886_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v_snd_2937_; lean_object* v_fst_2938_; lean_object* v_fst_2939_; lean_object* v_snd_2940_; lean_object* v___x_2941_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v_snd_2937_ = lean_ctor_get(v_a_2936_, 1);
lean_inc(v_snd_2937_);
v_fst_2938_ = lean_ctor_get(v_a_2936_, 0);
lean_inc(v_fst_2938_);
lean_dec(v_a_2936_);
v_fst_2939_ = lean_ctor_get(v_snd_2937_, 0);
lean_inc(v_fst_2939_);
v_snd_2940_ = lean_ctor_get(v_snd_2937_, 1);
lean_inc(v_snd_2940_);
lean_dec(v_snd_2937_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v___x_2930_);
v___x_2941_ = lean_whnf(v_snd_2940_, v___x_2930_, v_a_2884_, v_a_2885_, v_a_2886_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___f_2943_; uint8_t v___x_2944_; lean_object* v___x_2945_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
lean_inc(v_a_2932_);
v___f_2943_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2943_, 0, v_a_2942_);
lean_closure_set(v___f_2943_, 1, v_fst_2938_);
lean_closure_set(v___f_2943_, 2, v_fst_2939_);
lean_closure_set(v___f_2943_, 3, v_inst_2881_);
lean_closure_set(v___f_2943_, 4, v_a_2932_);
lean_closure_set(v___f_2943_, 5, v_projInfo_x3f_2882_);
v___x_2944_ = 0;
v___x_2945_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2932_, v___f_2943_, v___x_2944_, v___x_2944_, v___x_2930_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec_ref(v___x_2930_);
return v___x_2945_;
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_fst_2939_);
lean_dec(v_fst_2938_);
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2930_);
lean_dec(v_projInfo_x3f_2882_);
lean_dec_ref(v_inst_2881_);
v_a_2946_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2941_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2941_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2930_);
lean_dec(v_projInfo_x3f_2882_);
lean_dec_ref(v_inst_2881_);
v_a_2954_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2935_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2935_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec_ref(v___x_2930_);
lean_dec(v_projInfo_x3f_2882_);
lean_dec_ref(v_inst_2881_);
v_a_2962_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2931_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2931_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_2972_, lean_object* v_projInfo_x3f_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_2972_, v_projInfo_x3f_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_2980_, lean_object* v___x_2981_, lean_object* v_a_2982_, lean_object* v_inst_2983_, lean_object* v_R_2984_, lean_object* v_a_2985_, lean_object* v_b_2986_, lean_object* v_c_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2980_, v___x_2981_, v_a_2982_, v_a_2985_, v_b_2986_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_2994_, lean_object* v___x_2995_, lean_object* v_a_2996_, lean_object* v_inst_2997_, lean_object* v_R_2998_, lean_object* v_a_2999_, lean_object* v_b_3000_, lean_object* v_c_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_2994_, v___x_2995_, v_a_2996_, v_inst_2997_, v_R_2998_, v_a_2999_, v_b_3000_, v_c_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_a_2996_);
lean_dec(v___x_2995_);
lean_dec(v_upperBound_2994_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3008_, lean_object* v_msg_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3016_, lean_object* v_msg_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3016_, v_msg_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v_env_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3027_ = lean_st_ref_get(v___y_3025_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3029_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3028_, v_declName_3024_);
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3031_, v___y_3032_);
lean_dec(v___y_3032_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3035_, v___y_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3049_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3055_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
lean_ctor_set(v___x_3055_, 3, v___x_3054_);
lean_ctor_set(v___x_3055_, 4, v___x_3054_);
lean_ctor_set(v___x_3055_, 5, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3056_, lean_object* v_b_3057_, uint8_t v_kind_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_currNamespace_3063_; lean_object* v___x_3064_; lean_object* v_env_3065_; lean_object* v_nextMacroScope_3066_; lean_object* v_ngen_3067_; lean_object* v_auxDeclNGen_3068_; lean_object* v_traceState_3069_; lean_object* v_messages_3070_; lean_object* v_infoState_3071_; lean_object* v_snapshotTasks_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3099_; 
v_currNamespace_3063_ = lean_ctor_get(v___y_3060_, 6);
v___x_3064_ = lean_st_ref_take(v___y_3061_);
v_env_3065_ = lean_ctor_get(v___x_3064_, 0);
v_nextMacroScope_3066_ = lean_ctor_get(v___x_3064_, 1);
v_ngen_3067_ = lean_ctor_get(v___x_3064_, 2);
v_auxDeclNGen_3068_ = lean_ctor_get(v___x_3064_, 3);
v_traceState_3069_ = lean_ctor_get(v___x_3064_, 4);
v_messages_3070_ = lean_ctor_get(v___x_3064_, 6);
v_infoState_3071_ = lean_ctor_get(v___x_3064_, 7);
v_snapshotTasks_3072_ = lean_ctor_get(v___x_3064_, 8);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3064_, 5);
lean_dec(v_unused_3100_);
v___x_3074_ = v___x_3064_;
v_isShared_3075_ = v_isSharedCheck_3099_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_snapshotTasks_3072_);
lean_inc(v_infoState_3071_);
lean_inc(v_messages_3070_);
lean_inc(v_traceState_3069_);
lean_inc(v_auxDeclNGen_3068_);
lean_inc(v_ngen_3067_);
lean_inc(v_nextMacroScope_3066_);
lean_inc(v_env_3065_);
lean_dec(v___x_3064_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3099_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_inc(v_currNamespace_3063_);
v___x_3076_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3065_, v_ext_3056_, v_b_3057_, v_kind_3058_, v_currNamespace_3063_);
v___x_3077_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 5, v___x_3077_);
lean_ctor_set(v___x_3074_, 0, v___x_3076_);
v___x_3079_ = v___x_3074_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_nextMacroScope_3066_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_ngen_3067_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_auxDeclNGen_3068_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_traceState_3069_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_messages_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_infoState_3071_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_snapshotTasks_3072_);
v___x_3079_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_mctx_3082_; lean_object* v_zetaDeltaFVarIds_3083_; lean_object* v_postponed_3084_; lean_object* v_diag_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3096_; 
v___x_3080_ = lean_st_ref_set(v___y_3061_, v___x_3079_);
v___x_3081_ = lean_st_ref_take(v___y_3059_);
v_mctx_3082_ = lean_ctor_get(v___x_3081_, 0);
v_zetaDeltaFVarIds_3083_ = lean_ctor_get(v___x_3081_, 2);
v_postponed_3084_ = lean_ctor_get(v___x_3081_, 3);
v_diag_3085_ = lean_ctor_get(v___x_3081_, 4);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v___x_3081_, 1);
lean_dec(v_unused_3097_);
v___x_3087_ = v___x_3081_;
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_diag_3085_);
lean_inc(v_postponed_3084_);
lean_inc(v_zetaDeltaFVarIds_3083_);
lean_inc(v_mctx_3082_);
lean_dec(v___x_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_mctx_3082_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_zetaDeltaFVarIds_3083_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_postponed_3084_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_diag_3085_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_st_ref_set(v___y_3059_, v___x_3091_);
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3101_, lean_object* v_b_3102_, lean_object* v_kind_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
uint8_t v_kind_boxed_3108_; lean_object* v_res_3109_; 
v_kind_boxed_3108_ = lean_unbox(v_kind_3103_);
v_res_3109_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3101_, v_b_3102_, v_kind_boxed_3108_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_00_u03c3_3112_, lean_object* v_ext_3113_, lean_object* v_b_3114_, uint8_t v_kind_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3113_, v_b_3114_, v_kind_3115_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_00_u03b2_3123_, lean_object* v_00_u03c3_3124_, lean_object* v_ext_3125_, lean_object* v_b_3126_, lean_object* v_kind_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
uint8_t v_kind_boxed_3133_; lean_object* v_res_3134_; 
v_kind_boxed_3133_ = lean_unbox(v_kind_3127_);
v_res_3134_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3122_, v_00_u03b2_3123_, v_00_u03c3_3124_, v_ext_3125_, v_b_3126_, v_kind_boxed_3133_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v_env_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3138_ = lean_st_ref_get(v___y_3136_);
v_env_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3139_);
lean_dec(v___x_3138_);
v___x_3140_ = lean_get_reducibility_status(v_env_3139_, v_declName_3135_);
v___x_3141_ = lean_box(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3143_, v___y_3144_);
lean_dec(v___y_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3147_, v___y_3151_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v_res_3160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
lean_ctor_set(v___x_3166_, 3, v___x_3165_);
lean_ctor_set(v___x_3166_, 4, v___x_3164_);
lean_ctor_set(v___x_3166_, 5, v___x_3164_);
lean_ctor_set(v___x_3166_, 6, v___x_3164_);
lean_ctor_set(v___x_3166_, 7, v___x_3164_);
lean_ctor_set(v___x_3166_, 8, v___x_3164_);
lean_ctor_set(v___x_3166_, 9, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_unsigned_to_nat(32u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3170_ = ((size_t)5ULL);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_unsigned_to_nat(32u);
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_3172_);
v___x_3174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3175_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
lean_ctor_set(v___x_3175_, 2, v___x_3171_);
lean_ctor_set(v___x_3175_, 3, v___x_3171_);
lean_ctor_set_usize(v___x_3175_, 4, v___x_3170_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = lean_box(1);
v___x_3177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
lean_ctor_set(v___x_3179_, 2, v___x_3176_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3201_, lean_object* v_declHint_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; lean_object* v_env_3206_; uint8_t v___x_3207_; 
v___x_3205_ = lean_st_ref_get(v___y_3203_);
v_env_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc_ref(v_env_3206_);
lean_dec(v___x_3205_);
v___x_3207_ = l_Lean_Name_isAnonymous(v_declHint_3202_);
if (v___x_3207_ == 0)
{
uint8_t v_isExporting_3208_; 
v_isExporting_3208_ = lean_ctor_get_uint8(v_env_3206_, sizeof(void*)*8);
if (v_isExporting_3208_ == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref(v_env_3206_);
lean_dec(v_declHint_3202_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v_msg_3201_);
return v___x_3209_;
}
else
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
lean_inc_ref(v_env_3206_);
v___x_3210_ = l_Lean_Environment_setExporting(v_env_3206_, v___x_3207_);
lean_inc(v_declHint_3202_);
lean_inc_ref(v___x_3210_);
v___x_3211_ = l_Lean_Environment_contains(v___x_3210_, v_declHint_3202_, v_isExporting_3208_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v___x_3210_);
lean_dec_ref(v_env_3206_);
lean_dec(v_declHint_3202_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_msg_3201_);
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_c_3218_; lean_object* v___x_3219_; 
v___x_3213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3215_ = l_Lean_Options_empty;
v___x_3216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3210_);
lean_ctor_set(v___x_3216_, 1, v___x_3213_);
lean_ctor_set(v___x_3216_, 2, v___x_3214_);
lean_ctor_set(v___x_3216_, 3, v___x_3215_);
lean_inc(v_declHint_3202_);
v___x_3217_ = l_Lean_MessageData_ofConstName(v_declHint_3202_, v___x_3207_);
v_c_3218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3218_, 0, v___x_3216_);
lean_ctor_set(v_c_3218_, 1, v___x_3217_);
v___x_3219_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3206_, v_declHint_3202_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec_ref(v_env_3206_);
lean_dec(v_declHint_3202_);
v___x_3220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_c_3218_);
v___x_3222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l_Lean_MessageData_note(v___x_3223_);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v_msg_3201_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
else
{
lean_object* v_val_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3262_; 
v_val_3227_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3229_ = v___x_3219_;
v_isShared_3230_ = v_isSharedCheck_3262_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_val_3227_);
lean_dec(v___x_3219_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3262_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v_mod_3234_; uint8_t v___x_3235_; 
v___x_3231_ = lean_box(0);
v___x_3232_ = l_Lean_Environment_header(v_env_3206_);
lean_dec_ref(v_env_3206_);
v___x_3233_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3232_);
v_mod_3234_ = lean_array_get(v___x_3231_, v___x_3233_, v_val_3227_);
lean_dec(v_val_3227_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = l_Lean_isPrivateName(v_declHint_3202_);
lean_dec(v_declHint_3202_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v_c_3218_);
v___x_3238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_MessageData_ofName(v_mod_3234_);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_MessageData_note(v___x_3243_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v_msg_3201_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3245_);
v___x_3247_ = v___x_3229_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v_c_3218_);
v___x_3251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_MessageData_ofName(v_mod_3234_);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_MessageData_note(v___x_3256_);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v_msg_3201_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3258_);
v___x_3260_ = v___x_3229_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3263_; 
lean_dec_ref(v_env_3206_);
lean_dec(v_declHint_3202_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_msg_3201_);
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3264_, lean_object* v_declHint_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3264_, v_declHint_3265_, v___y_3266_);
lean_dec(v___y_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3269_, lean_object* v_declHint_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3286_; 
v___x_3276_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3269_, v_declHint_3270_, v___y_3274_);
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3286_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3286_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3281_ = l_Lean_unknownIdentifierMessageTag;
v___x_3282_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v_a_3277_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3282_);
v___x_3284_ = v___x_3279_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3287_, lean_object* v_declHint_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3287_, v_declHint_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3295_, lean_object* v_msg_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_fileName_3302_; lean_object* v_fileMap_3303_; lean_object* v_options_3304_; lean_object* v_currRecDepth_3305_; lean_object* v_maxRecDepth_3306_; lean_object* v_ref_3307_; lean_object* v_currNamespace_3308_; lean_object* v_openDecls_3309_; lean_object* v_initHeartbeats_3310_; lean_object* v_maxHeartbeats_3311_; lean_object* v_quotContext_3312_; lean_object* v_currMacroScope_3313_; uint8_t v_diag_3314_; lean_object* v_cancelTk_x3f_3315_; uint8_t v_suppressElabErrors_3316_; lean_object* v_inheritedTraceOptions_3317_; lean_object* v_ref_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_fileName_3302_ = lean_ctor_get(v___y_3299_, 0);
v_fileMap_3303_ = lean_ctor_get(v___y_3299_, 1);
v_options_3304_ = lean_ctor_get(v___y_3299_, 2);
v_currRecDepth_3305_ = lean_ctor_get(v___y_3299_, 3);
v_maxRecDepth_3306_ = lean_ctor_get(v___y_3299_, 4);
v_ref_3307_ = lean_ctor_get(v___y_3299_, 5);
v_currNamespace_3308_ = lean_ctor_get(v___y_3299_, 6);
v_openDecls_3309_ = lean_ctor_get(v___y_3299_, 7);
v_initHeartbeats_3310_ = lean_ctor_get(v___y_3299_, 8);
v_maxHeartbeats_3311_ = lean_ctor_get(v___y_3299_, 9);
v_quotContext_3312_ = lean_ctor_get(v___y_3299_, 10);
v_currMacroScope_3313_ = lean_ctor_get(v___y_3299_, 11);
v_diag_3314_ = lean_ctor_get_uint8(v___y_3299_, sizeof(void*)*14);
v_cancelTk_x3f_3315_ = lean_ctor_get(v___y_3299_, 12);
v_suppressElabErrors_3316_ = lean_ctor_get_uint8(v___y_3299_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3317_ = lean_ctor_get(v___y_3299_, 13);
v_ref_3318_ = l_Lean_replaceRef(v_ref_3295_, v_ref_3307_);
lean_inc_ref(v_inheritedTraceOptions_3317_);
lean_inc(v_cancelTk_x3f_3315_);
lean_inc(v_currMacroScope_3313_);
lean_inc(v_quotContext_3312_);
lean_inc(v_maxHeartbeats_3311_);
lean_inc(v_initHeartbeats_3310_);
lean_inc(v_openDecls_3309_);
lean_inc(v_currNamespace_3308_);
lean_inc(v_maxRecDepth_3306_);
lean_inc(v_currRecDepth_3305_);
lean_inc_ref(v_options_3304_);
lean_inc_ref(v_fileMap_3303_);
lean_inc_ref(v_fileName_3302_);
v___x_3319_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3319_, 0, v_fileName_3302_);
lean_ctor_set(v___x_3319_, 1, v_fileMap_3303_);
lean_ctor_set(v___x_3319_, 2, v_options_3304_);
lean_ctor_set(v___x_3319_, 3, v_currRecDepth_3305_);
lean_ctor_set(v___x_3319_, 4, v_maxRecDepth_3306_);
lean_ctor_set(v___x_3319_, 5, v_ref_3318_);
lean_ctor_set(v___x_3319_, 6, v_currNamespace_3308_);
lean_ctor_set(v___x_3319_, 7, v_openDecls_3309_);
lean_ctor_set(v___x_3319_, 8, v_initHeartbeats_3310_);
lean_ctor_set(v___x_3319_, 9, v_maxHeartbeats_3311_);
lean_ctor_set(v___x_3319_, 10, v_quotContext_3312_);
lean_ctor_set(v___x_3319_, 11, v_currMacroScope_3313_);
lean_ctor_set(v___x_3319_, 12, v_cancelTk_x3f_3315_);
lean_ctor_set(v___x_3319_, 13, v_inheritedTraceOptions_3317_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*14, v_diag_3314_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*14 + 1, v_suppressElabErrors_3316_);
v___x_3320_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3296_, v___y_3297_, v___y_3298_, v___x_3319_, v___y_3300_);
lean_dec_ref(v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3321_, lean_object* v_msg_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3321_, v_msg_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v_ref_3321_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3329_, lean_object* v_msg_3330_, lean_object* v_declHint_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3339_; 
v___x_3337_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3330_, v_declHint_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3329_, v_a_3338_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3340_, lean_object* v_msg_3341_, lean_object* v_declHint_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3340_, v_msg_3341_, v_declHint_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v_ref_3340_);
return v_res_3348_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3352_, lean_object* v_constName_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3359_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3360_ = 0;
lean_inc(v_constName_3353_);
v___x_3361_ = l_Lean_MessageData_ofConstName(v_constName_3353_, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3359_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3352_, v___x_3364_, v_constName_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3366_, lean_object* v_constName_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3366_, v_constName_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v_ref_3366_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_ref_3380_; lean_object* v___x_3381_; 
v_ref_3380_ = lean_ctor_get(v___y_3377_, 5);
v___x_3381_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3380_, v_constName_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; lean_object* v_env_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = lean_st_ref_get(v___y_3393_);
v_env_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_env_3396_);
lean_dec(v___x_3395_);
v___x_3397_ = 0;
lean_inc(v_constName_3389_);
v___x_3398_ = l_Lean_Environment_find_x3f(v_env_3396_, v_constName_3389_, v___x_3397_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v___x_3399_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_constName_3389_);
v_val_3400_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3398_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_val_3400_);
lean_dec(v___x_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 0);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_val_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
return v_res_3414_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3422_, uint8_t v_suppressElabErrors_3423_, lean_object* v_x_3424_){
_start:
{
if (lean_obj_tag(v_x_3424_) == 1)
{
lean_object* v_pre_3425_; 
v_pre_3425_ = lean_ctor_get(v_x_3424_, 0);
switch(lean_obj_tag(v_pre_3425_))
{
case 1:
{
lean_object* v_pre_3426_; 
v_pre_3426_ = lean_ctor_get(v_pre_3425_, 0);
switch(lean_obj_tag(v_pre_3426_))
{
case 0:
{
lean_object* v_str_3427_; lean_object* v_str_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v_str_3427_ = lean_ctor_get(v_x_3424_, 1);
v_str_3428_ = lean_ctor_get(v_pre_3425_, 1);
v___x_3429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3430_ = lean_string_dec_eq(v_str_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3432_ = lean_string_dec_eq(v_str_3428_, v___x_3431_);
if (v___x_3432_ == 0)
{
return v___y_3422_;
}
else
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3434_ = lean_string_dec_eq(v_str_3427_, v___x_3433_);
if (v___x_3434_ == 0)
{
return v___y_3422_;
}
else
{
return v_suppressElabErrors_3423_;
}
}
}
else
{
lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3436_ = lean_string_dec_eq(v_str_3427_, v___x_3435_);
if (v___x_3436_ == 0)
{
return v___y_3422_;
}
else
{
return v_suppressElabErrors_3423_;
}
}
}
case 1:
{
lean_object* v_pre_3437_; 
v_pre_3437_ = lean_ctor_get(v_pre_3426_, 0);
if (lean_obj_tag(v_pre_3437_) == 0)
{
lean_object* v_str_3438_; lean_object* v_str_3439_; lean_object* v_str_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_str_3438_ = lean_ctor_get(v_x_3424_, 1);
v_str_3439_ = lean_ctor_get(v_pre_3425_, 1);
v_str_3440_ = lean_ctor_get(v_pre_3426_, 1);
v___x_3441_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3442_ = lean_string_dec_eq(v_str_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
return v___y_3422_;
}
else
{
lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3443_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3444_ = lean_string_dec_eq(v_str_3439_, v___x_3443_);
if (v___x_3444_ == 0)
{
return v___y_3422_;
}
else
{
lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3446_ = lean_string_dec_eq(v_str_3438_, v___x_3445_);
if (v___x_3446_ == 0)
{
return v___y_3422_;
}
else
{
return v_suppressElabErrors_3423_;
}
}
}
}
else
{
return v___y_3422_;
}
}
default: 
{
return v___y_3422_;
}
}
}
case 0:
{
lean_object* v_str_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_str_3447_ = lean_ctor_get(v_x_3424_, 1);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3449_ = lean_string_dec_eq(v_str_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
return v___y_3422_;
}
else
{
return v_suppressElabErrors_3423_;
}
}
default: 
{
return v___y_3422_;
}
}
}
else
{
return v___y_3422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3450_, lean_object* v_suppressElabErrors_3451_, lean_object* v_x_3452_){
_start:
{
uint8_t v___y_8288__boxed_3453_; uint8_t v_suppressElabErrors_boxed_3454_; uint8_t v_res_3455_; lean_object* v_r_3456_; 
v___y_8288__boxed_3453_ = lean_unbox(v___y_3450_);
v_suppressElabErrors_boxed_3454_ = lean_unbox(v_suppressElabErrors_3451_);
v_res_3455_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8288__boxed_3453_, v_suppressElabErrors_boxed_3454_, v_x_3452_);
lean_dec(v_x_3452_);
v_r_3456_ = lean_box(v_res_3455_);
return v_r_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3457_, lean_object* v_msgData_3458_, uint8_t v_severity_3459_, uint8_t v_isSilent_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; uint8_t v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; uint8_t v___y_3544_; uint8_t v___y_3545_; uint8_t v___x_3550_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; uint8_t v___y_3557_; uint8_t v___y_3558_; uint8_t v___y_3560_; uint8_t v___x_3575_; 
v___x_3550_ = 2;
v___x_3575_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3459_, v___x_3550_);
if (v___x_3575_ == 0)
{
v___y_3560_ = v___x_3575_;
goto v___jp_3559_;
}
else
{
uint8_t v___x_3576_; 
lean_inc_ref(v_msgData_3458_);
v___x_3576_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3458_);
v___y_3560_ = v___x_3576_;
goto v___jp_3559_;
}
v___jp_3466_:
{
lean_object* v___x_3476_; lean_object* v_currNamespace_3477_; lean_object* v_openDecls_3478_; lean_object* v_env_3479_; lean_object* v_nextMacroScope_3480_; lean_object* v_ngen_3481_; lean_object* v_auxDeclNGen_3482_; lean_object* v_traceState_3483_; lean_object* v_cache_3484_; lean_object* v_messages_3485_; lean_object* v_infoState_3486_; lean_object* v_snapshotTasks_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3501_; 
v___x_3476_ = lean_st_ref_take(v___y_3475_);
v_currNamespace_3477_ = lean_ctor_get(v___y_3474_, 6);
v_openDecls_3478_ = lean_ctor_get(v___y_3474_, 7);
v_env_3479_ = lean_ctor_get(v___x_3476_, 0);
v_nextMacroScope_3480_ = lean_ctor_get(v___x_3476_, 1);
v_ngen_3481_ = lean_ctor_get(v___x_3476_, 2);
v_auxDeclNGen_3482_ = lean_ctor_get(v___x_3476_, 3);
v_traceState_3483_ = lean_ctor_get(v___x_3476_, 4);
v_cache_3484_ = lean_ctor_get(v___x_3476_, 5);
v_messages_3485_ = lean_ctor_get(v___x_3476_, 6);
v_infoState_3486_ = lean_ctor_get(v___x_3476_, 7);
v_snapshotTasks_3487_ = lean_ctor_get(v___x_3476_, 8);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3489_ = v___x_3476_;
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snapshotTasks_3487_);
lean_inc(v_infoState_3486_);
lean_inc(v_messages_3485_);
lean_inc(v_cache_3484_);
lean_inc(v_traceState_3483_);
lean_inc(v_auxDeclNGen_3482_);
lean_inc(v_ngen_3481_);
lean_inc(v_nextMacroScope_3480_);
lean_inc(v_env_3479_);
lean_dec(v___x_3476_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
lean_inc(v_openDecls_3478_);
lean_inc(v_currNamespace_3477_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v_currNamespace_3477_);
lean_ctor_set(v___x_3491_, 1, v_openDecls_3478_);
v___x_3492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
lean_ctor_set(v___x_3492_, 1, v___y_3468_);
lean_inc_ref(v___y_3472_);
lean_inc_ref(v___y_3467_);
v___x_3493_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3493_, 0, v___y_3467_);
lean_ctor_set(v___x_3493_, 1, v___y_3473_);
lean_ctor_set(v___x_3493_, 2, v___y_3471_);
lean_ctor_set(v___x_3493_, 3, v___y_3472_);
lean_ctor_set(v___x_3493_, 4, v___x_3492_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*5, v___y_3470_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*5 + 1, v___y_3469_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*5 + 2, v_isSilent_3460_);
v___x_3494_ = l_Lean_MessageLog_add(v___x_3493_, v_messages_3485_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 6, v___x_3494_);
v___x_3496_ = v___x_3489_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_env_3479_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_nextMacroScope_3480_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_ngen_3481_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_auxDeclNGen_3482_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v_traceState_3483_);
lean_ctor_set(v_reuseFailAlloc_3500_, 5, v_cache_3484_);
lean_ctor_set(v_reuseFailAlloc_3500_, 6, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3500_, 7, v_infoState_3486_);
lean_ctor_set(v_reuseFailAlloc_3500_, 8, v_snapshotTasks_3487_);
v___x_3496_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = lean_st_ref_set(v___y_3475_, v___x_3496_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
}
v___jp_3502_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3526_; 
v___x_3511_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3458_);
v___x_3512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3511_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3526_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3526_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_inc_ref_n(v___y_3506_, 2);
v___x_3517_ = l_Lean_FileMap_toPosition(v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
v___x_3518_ = l_Lean_FileMap_toPosition(v___y_3506_, v___y_3510_);
lean_dec(v___y_3510_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
v___x_3520_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3504_ == 0)
{
lean_del_object(v___x_3515_);
lean_dec_ref(v___y_3503_);
v___y_3467_ = v___y_3505_;
v___y_3468_ = v_a_3513_;
v___y_3469_ = v___y_3509_;
v___y_3470_ = v___y_3508_;
v___y_3471_ = v___x_3519_;
v___y_3472_ = v___x_3520_;
v___y_3473_ = v___x_3517_;
v___y_3474_ = v___y_3463_;
v___y_3475_ = v___y_3464_;
goto v___jp_3466_;
}
else
{
uint8_t v___x_3521_; 
lean_inc(v_a_3513_);
v___x_3521_ = l_Lean_MessageData_hasTag(v___y_3503_, v_a_3513_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref(v___x_3517_);
lean_dec(v_a_3513_);
v___x_3522_ = lean_box(0);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3522_);
v___x_3524_ = v___x_3515_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
else
{
lean_del_object(v___x_3515_);
v___y_3467_ = v___y_3505_;
v___y_3468_ = v_a_3513_;
v___y_3469_ = v___y_3509_;
v___y_3470_ = v___y_3508_;
v___y_3471_ = v___x_3519_;
v___y_3472_ = v___x_3520_;
v___y_3473_ = v___x_3517_;
v___y_3474_ = v___y_3463_;
v___y_3475_ = v___y_3464_;
goto v___jp_3466_;
}
}
}
}
v___jp_3527_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Syntax_getTailPos_x3f(v___y_3530_, v___y_3534_);
lean_dec(v___y_3530_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_inc(v___y_3535_);
v___y_3503_ = v___y_3528_;
v___y_3504_ = v___y_3529_;
v___y_3505_ = v___y_3532_;
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3535_;
goto v___jp_3502_;
}
else
{
lean_object* v_val_3537_; 
v_val_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref(v___x_3536_);
v___y_3503_ = v___y_3528_;
v___y_3504_ = v___y_3529_;
v___y_3505_ = v___y_3532_;
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v_val_3537_;
goto v___jp_3502_;
}
}
v___jp_3538_:
{
lean_object* v_ref_3546_; lean_object* v___x_3547_; 
v_ref_3546_ = l_Lean_replaceRef(v_ref_3457_, v___y_3543_);
v___x_3547_ = l_Lean_Syntax_getPos_x3f(v_ref_3546_, v___y_3544_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_unsigned_to_nat(0u);
v___y_3528_ = v___y_3539_;
v___y_3529_ = v___y_3540_;
v___y_3530_ = v_ref_3546_;
v___y_3531_ = v___y_3542_;
v___y_3532_ = v___y_3541_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v___y_3544_;
v___y_3535_ = v___x_3548_;
goto v___jp_3527_;
}
else
{
lean_object* v_val_3549_; 
v_val_3549_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_val_3549_);
lean_dec_ref(v___x_3547_);
v___y_3528_ = v___y_3539_;
v___y_3529_ = v___y_3540_;
v___y_3530_ = v_ref_3546_;
v___y_3531_ = v___y_3542_;
v___y_3532_ = v___y_3541_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v___y_3544_;
v___y_3535_ = v_val_3549_;
goto v___jp_3527_;
}
}
v___jp_3551_:
{
if (v___y_3558_ == 0)
{
v___y_3539_ = v___y_3553_;
v___y_3540_ = v___y_3552_;
v___y_3541_ = v___y_3555_;
v___y_3542_ = v___y_3554_;
v___y_3543_ = v___y_3556_;
v___y_3544_ = v___y_3557_;
v___y_3545_ = v_severity_3459_;
goto v___jp_3538_;
}
else
{
v___y_3539_ = v___y_3553_;
v___y_3540_ = v___y_3552_;
v___y_3541_ = v___y_3555_;
v___y_3542_ = v___y_3554_;
v___y_3543_ = v___y_3556_;
v___y_3544_ = v___y_3557_;
v___y_3545_ = v___x_3550_;
goto v___jp_3538_;
}
}
v___jp_3559_:
{
if (v___y_3560_ == 0)
{
lean_object* v_fileName_3561_; lean_object* v_fileMap_3562_; lean_object* v_options_3563_; lean_object* v_ref_3564_; uint8_t v_suppressElabErrors_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___f_3568_; uint8_t v___x_3569_; uint8_t v___x_3570_; 
v_fileName_3561_ = lean_ctor_get(v___y_3463_, 0);
v_fileMap_3562_ = lean_ctor_get(v___y_3463_, 1);
v_options_3563_ = lean_ctor_get(v___y_3463_, 2);
v_ref_3564_ = lean_ctor_get(v___y_3463_, 5);
v_suppressElabErrors_3565_ = lean_ctor_get_uint8(v___y_3463_, sizeof(void*)*14 + 1);
v___x_3566_ = lean_box(v___y_3560_);
v___x_3567_ = lean_box(v_suppressElabErrors_3565_);
v___f_3568_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3568_, 0, v___x_3566_);
lean_closure_set(v___f_3568_, 1, v___x_3567_);
v___x_3569_ = 1;
v___x_3570_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3459_, v___x_3569_);
if (v___x_3570_ == 0)
{
v___y_3552_ = v_suppressElabErrors_3565_;
v___y_3553_ = v___f_3568_;
v___y_3554_ = v_fileMap_3562_;
v___y_3555_ = v_fileName_3561_;
v___y_3556_ = v_ref_3564_;
v___y_3557_ = v___y_3560_;
v___y_3558_ = v___x_3570_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3571_ = l_Lean_warningAsError;
v___x_3572_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3563_, v___x_3571_);
v___y_3552_ = v_suppressElabErrors_3565_;
v___y_3553_ = v___f_3568_;
v___y_3554_ = v_fileMap_3562_;
v___y_3555_ = v_fileName_3561_;
v___y_3556_ = v_ref_3564_;
v___y_3557_ = v___y_3560_;
v___y_3558_ = v___x_3572_;
goto v___jp_3551_;
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_dec_ref(v_msgData_3458_);
v___x_3573_ = lean_box(0);
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3577_, lean_object* v_msgData_3578_, lean_object* v_severity_3579_, lean_object* v_isSilent_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
uint8_t v_severity_boxed_3586_; uint8_t v_isSilent_boxed_3587_; lean_object* v_res_3588_; 
v_severity_boxed_3586_ = lean_unbox(v_severity_3579_);
v_isSilent_boxed_3587_ = lean_unbox(v_isSilent_3580_);
v_res_3588_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3577_, v_msgData_3578_, v_severity_boxed_3586_, v_isSilent_boxed_3587_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v_ref_3577_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3589_, uint8_t v_severity_3590_, uint8_t v_isSilent_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_ref_3597_; lean_object* v___x_3598_; 
v_ref_3597_ = lean_ctor_get(v___y_3594_, 5);
v___x_3598_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3597_, v_msgData_3589_, v_severity_3590_, v_isSilent_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3599_, lean_object* v_severity_3600_, lean_object* v_isSilent_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
uint8_t v_severity_boxed_3607_; uint8_t v_isSilent_boxed_3608_; lean_object* v_res_3609_; 
v_severity_boxed_3607_ = lean_unbox(v_severity_3600_);
v_isSilent_boxed_3608_ = lean_unbox(v_isSilent_3601_);
v_res_3609_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3599_, v_severity_boxed_3607_, v_isSilent_boxed_3608_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
uint8_t v___x_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = 1;
v___x_3617_ = 0;
v___x_3618_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3610_, v___x_3616_, v___x_3617_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v_env_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; 
v___x_3632_ = lean_st_ref_get(v___y_3630_);
v_env_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc_ref(v_env_3633_);
lean_dec(v___x_3632_);
v___x_3634_ = 0;
lean_inc(v_constName_3626_);
v___x_3635_ = l_Lean_Environment_findConstVal_x3f(v_env_3633_, v_constName_3626_, v___x_3634_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3636_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_constName_3626_);
v_val_3637_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3635_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_val_3637_);
lean_dec(v___x_3635_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 0);
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_val_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
if (lean_obj_tag(v_a_3652_) == 0)
{
lean_object* v___x_3654_; 
v___x_3654_ = l_List_reverse___redArg(v_a_3653_);
return v___x_3654_;
}
else
{
lean_object* v_head_3655_; lean_object* v_tail_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3665_; 
v_head_3655_ = lean_ctor_get(v_a_3652_, 0);
v_tail_3656_ = lean_ctor_get(v_a_3652_, 1);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3658_ = v_a_3652_;
v_isShared_3659_ = v_isSharedCheck_3665_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_tail_3656_);
lean_inc(v_head_3655_);
lean_dec(v_a_3652_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3665_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3660_ = l_Lean_mkLevelParam(v_head_3655_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v_a_3653_);
lean_ctor_set(v___x_3658_, 0, v___x_3660_);
v___x_3662_ = v___x_3658_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_a_3653_);
v___x_3662_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
v_a_3652_ = v_tail_3656_;
v_a_3653_ = v___x_3662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
lean_inc(v_constName_3666_);
v___x_3672_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3684_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3684_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3684_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_levelParams_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v_levelParams_3677_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_levelParams_3677_);
lean_dec(v_a_3673_);
v___x_3678_ = lean_box(0);
v___x_3679_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_3677_, v___x_3678_);
v___x_3680_ = l_Lean_mkConst(v_constName_3666_, v___x_3679_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3680_);
v___x_3682_ = v___x_3675_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_constName_3666_);
v_a_3685_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3672_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3672_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3699_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_3709_, uint8_t v_attrKind_3710_, lean_object* v_prio_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___x_3717_; 
lean_inc(v_declName_3709_);
v___x_3717_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_3709_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc_n(v_a_3718_, 2);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_3718_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___x_3748_; lean_object* v_a_3749_; uint8_t v___x_3750_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
lean_inc(v_declName_3709_);
v___x_3748_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3709_, v_a_3715_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref(v___x_3748_);
v___x_3750_ = lean_unbox(v_a_3749_);
lean_dec(v_a_3749_);
switch(v___x_3750_)
{
case 0:
{
v___y_3722_ = v_a_3712_;
v___y_3723_ = v_a_3713_;
v___y_3724_ = v_a_3714_;
v___y_3725_ = v_a_3715_;
goto v___jp_3721_;
}
case 3:
{
v___y_3722_ = v_a_3712_;
v___y_3723_ = v_a_3713_;
v___y_3724_ = v_a_3714_;
v___y_3725_ = v_a_3715_;
goto v___jp_3721_;
}
default: 
{
lean_object* v___x_3751_; 
lean_inc(v_declName_3709_);
v___x_3751_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_3709_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; uint8_t v___x_3753_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref(v___x_3751_);
v___x_3753_ = l_Lean_ConstantInfo_isDefinition(v_a_3752_);
lean_dec(v_a_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v_env_3755_; uint8_t v___x_3756_; 
v___x_3754_ = lean_st_ref_get(v_a_3715_);
v_env_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc_ref(v_env_3755_);
lean_dec(v___x_3754_);
lean_inc(v_declName_3709_);
v___x_3756_ = l_Lean_wasOriginallyDefn(v_env_3755_, v_declName_3709_);
if (v___x_3756_ == 0)
{
v___y_3722_ = v_a_3712_;
v___y_3723_ = v_a_3713_;
v___y_3724_ = v_a_3714_;
v___y_3725_ = v_a_3715_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3757_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3709_);
v___x_3758_ = l_Lean_MessageData_ofName(v_declName_3709_);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3761_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref(v___x_3762_);
v___y_3722_ = v_a_3712_;
v___y_3723_ = v_a_3713_;
v___y_3724_ = v_a_3714_;
v___y_3725_ = v_a_3715_;
goto v___jp_3721_;
}
else
{
lean_dec(v_a_3720_);
lean_dec(v_a_3718_);
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
return v___x_3762_;
}
}
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3763_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3709_);
v___x_3764_ = l_Lean_MessageData_ofName(v_declName_3709_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3767_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_dec_ref(v___x_3768_);
v___y_3722_ = v_a_3712_;
v___y_3723_ = v_a_3713_;
v___y_3724_ = v_a_3714_;
v___y_3725_ = v_a_3715_;
goto v___jp_3721_;
}
else
{
lean_dec(v_a_3720_);
lean_dec(v_a_3718_);
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
return v___x_3768_;
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec(v_a_3720_);
lean_dec(v_a_3718_);
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
v_a_3769_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3751_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3751_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
v___jp_3721_:
{
lean_object* v___x_3726_; lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3747_; 
lean_inc(v_declName_3709_);
v___x_3726_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3709_, v___y_3725_);
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3747_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3747_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; 
lean_inc(v_a_3718_);
v___x_3731_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_3718_, v_a_3727_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = l_Lean_Meta_instanceExtension;
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 1);
lean_ctor_set(v___x_3729_, 0, v_declName_3709_);
v___x_3735_ = v___x_3729_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_declName_3709_);
v___x_3735_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3736_, 0, v_a_3720_);
lean_ctor_set(v___x_3736_, 1, v_a_3718_);
lean_ctor_set(v___x_3736_, 2, v_prio_3711_);
lean_ctor_set(v___x_3736_, 3, v___x_3735_);
lean_ctor_set(v___x_3736_, 4, v_a_3732_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*5, v_attrKind_3710_);
v___x_3737_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_3733_, v___x_3736_, v_attrKind_3710_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3737_;
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3729_);
lean_dec(v_a_3720_);
lean_dec(v_a_3718_);
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
v_a_3739_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3731_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3731_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
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
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_a_3718_);
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
v_a_3777_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3719_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3719_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v_prio_3711_);
lean_dec(v_declName_3709_);
v_a_3785_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3717_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3717_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_3793_, lean_object* v_attrKind_3794_, lean_object* v_prio_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
uint8_t v_attrKind_boxed_3801_; lean_object* v_res_3802_; 
v_attrKind_boxed_3801_ = lean_unbox(v_attrKind_3794_);
v_res_3802_ = l_Lean_Meta_addInstance(v_declName_3793_, v_attrKind_boxed_3801_, v_prio_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_3803_, lean_object* v_constName_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_constName_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_3811_, v_constName_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_constName_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3820_, v_constName_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_3828_, lean_object* v_ref_3829_, lean_object* v_constName_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_3828_, v_ref_3829_, v_constName_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v_ref_3829_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_3837_, lean_object* v_ref_3838_, lean_object* v_msg_3839_, lean_object* v_declHint_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3838_, v_msg_3839_, v_declHint_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3847_, lean_object* v_ref_3848_, lean_object* v_msg_3849_, lean_object* v_declHint_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_3847_, v_ref_3848_, v_msg_3849_, v_declHint_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v_ref_3848_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_3857_, lean_object* v_declHint_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3857_, v_declHint_3858_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_3865_, lean_object* v_declHint_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_3865_, v_declHint_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_3873_, lean_object* v_ref_3874_, lean_object* v_msg_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3874_, v_msg_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3882_, lean_object* v_ref_3883_, lean_object* v_msg_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_3882_, v_ref_3883_, v_msg_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v_ref_3883_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_3891_, uint8_t v_s_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v_env_3897_; lean_object* v_nextMacroScope_3898_; lean_object* v_ngen_3899_; lean_object* v_auxDeclNGen_3900_; lean_object* v_traceState_3901_; lean_object* v_messages_3902_; lean_object* v_infoState_3903_; lean_object* v_snapshotTasks_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3933_; 
v___x_3896_ = lean_st_ref_take(v___y_3894_);
v_env_3897_ = lean_ctor_get(v___x_3896_, 0);
v_nextMacroScope_3898_ = lean_ctor_get(v___x_3896_, 1);
v_ngen_3899_ = lean_ctor_get(v___x_3896_, 2);
v_auxDeclNGen_3900_ = lean_ctor_get(v___x_3896_, 3);
v_traceState_3901_ = lean_ctor_get(v___x_3896_, 4);
v_messages_3902_ = lean_ctor_get(v___x_3896_, 6);
v_infoState_3903_ = lean_ctor_get(v___x_3896_, 7);
v_snapshotTasks_3904_ = lean_ctor_get(v___x_3896_, 8);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v___x_3896_, 5);
lean_dec(v_unused_3934_);
v___x_3906_ = v___x_3896_;
v_isShared_3907_ = v_isSharedCheck_3933_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_snapshotTasks_3904_);
lean_inc(v_infoState_3903_);
lean_inc(v_messages_3902_);
lean_inc(v_traceState_3901_);
lean_inc(v_auxDeclNGen_3900_);
lean_inc(v_ngen_3899_);
lean_inc(v_nextMacroScope_3898_);
lean_inc(v_env_3897_);
lean_dec(v___x_3896_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3933_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3908_ = 0;
v___x_3909_ = lean_box(0);
v___x_3910_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_3897_, v_declName_3891_, v_s_3892_, v___x_3908_, v___x_3909_);
v___x_3911_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 5, v___x_3911_);
lean_ctor_set(v___x_3906_, 0, v___x_3910_);
v___x_3913_ = v___x_3906_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_nextMacroScope_3898_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_ngen_3899_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_auxDeclNGen_3900_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_traceState_3901_);
lean_ctor_set(v_reuseFailAlloc_3932_, 5, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3932_, 6, v_messages_3902_);
lean_ctor_set(v_reuseFailAlloc_3932_, 7, v_infoState_3903_);
lean_ctor_set(v_reuseFailAlloc_3932_, 8, v_snapshotTasks_3904_);
v___x_3913_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v_mctx_3916_; lean_object* v_zetaDeltaFVarIds_3917_; lean_object* v_postponed_3918_; lean_object* v_diag_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3930_; 
v___x_3914_ = lean_st_ref_set(v___y_3894_, v___x_3913_);
v___x_3915_ = lean_st_ref_take(v___y_3893_);
v_mctx_3916_ = lean_ctor_get(v___x_3915_, 0);
v_zetaDeltaFVarIds_3917_ = lean_ctor_get(v___x_3915_, 2);
v_postponed_3918_ = lean_ctor_get(v___x_3915_, 3);
v_diag_3919_ = lean_ctor_get(v___x_3915_, 4);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v___x_3915_, 1);
lean_dec(v_unused_3931_);
v___x_3921_ = v___x_3915_;
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_diag_3919_);
lean_inc(v_postponed_3918_);
lean_inc(v_zetaDeltaFVarIds_3917_);
lean_inc(v_mctx_3916_);
lean_dec(v___x_3915_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_mctx_3916_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_zetaDeltaFVarIds_3917_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_postponed_3918_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_diag_3919_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_st_ref_set(v___y_3893_, v___x_3925_);
v___x_3927_ = lean_box(0);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_3935_, lean_object* v_s_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
uint8_t v_s_boxed_3940_; lean_object* v_res_3941_; 
v_s_boxed_3940_ = lean_unbox(v_s_3936_);
v_res_3941_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3935_, v_s_boxed_3940_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec(v___y_3937_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_3942_, uint8_t v_s_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3942_, v_s_3943_, v___y_3945_, v___y_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_3950_, lean_object* v_s_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v_s_boxed_3957_; lean_object* v_res_3958_; 
v_s_boxed_3957_ = lean_unbox(v_s_3951_);
v_res_3958_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_3950_, v_s_boxed_3957_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_3959_, uint8_t v_attrKind_3960_, lean_object* v_prio_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = 3;
lean_inc(v_declName_3959_);
v___x_3968_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3959_, v___x_3967_, v_a_3963_, v_a_3965_);
lean_dec_ref(v___x_3968_);
v___x_3969_ = l_Lean_Meta_addInstance(v_declName_3959_, v_attrKind_3960_, v_prio_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_3970_, lean_object* v_attrKind_3971_, lean_object* v_prio_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
uint8_t v_attrKind_boxed_3978_; lean_object* v_res_3979_; 
v_attrKind_boxed_3978_ = lean_unbox(v_attrKind_3971_);
v_res_3979_ = l_Lean_Meta_registerInstance(v_declName_3970_, v_attrKind_boxed_3978_, v_prio_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_3980_, lean_object* v_x_3981_){
_start:
{
lean_inc_ref(v_a_3980_);
return v_a_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_3982_, lean_object* v_x_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_3982_, v_x_3983_);
lean_dec_ref(v_x_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; lean_object* v_env_3990_; lean_object* v_options_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3989_ = lean_st_ref_get(v___y_3987_);
v_env_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_3990_);
lean_dec(v___x_3989_);
v_options_3991_ = lean_ctor_get(v___y_3986_, 2);
v___x_3992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3993_ = lean_unsigned_to_nat(32u);
v___x_3994_ = lean_mk_empty_array_with_capacity(v___x_3993_);
lean_dec_ref(v___x_3994_);
v___x_3995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3991_);
v___x_3996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3996_, 0, v_env_3990_);
lean_ctor_set(v___x_3996_, 1, v___x_3992_);
lean_ctor_set(v___x_3996_, 2, v___x_3995_);
lean_ctor_set(v___x_3996_, 3, v_options_3991_);
v___x_3997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v_msgData_3985_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_3999_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_ref_4008_; lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4018_; 
v_ref_4008_ = lean_ctor_get(v___y_4005_, 5);
v___x_4009_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4004_, v___y_4005_, v___y_4006_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4018_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4018_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4016_; 
lean_inc(v_ref_4008_);
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_ref_4008_);
lean_ctor_set(v___x_4014_, 1, v_a_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 1);
lean_ctor_set(v___x_4012_, 0, v___x_4014_);
v___x_4016_ = v___x_4012_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4024_, lean_object* v_i_4025_, lean_object* v_k_4026_){
_start:
{
lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4027_ = lean_array_get_size(v_keys_4024_);
v___x_4028_ = lean_nat_dec_lt(v_i_4025_, v___x_4027_);
if (v___x_4028_ == 0)
{
lean_dec(v_i_4025_);
return v___x_4028_;
}
else
{
lean_object* v_k_x27_4029_; uint8_t v___x_4030_; 
v_k_x27_4029_ = lean_array_fget_borrowed(v_keys_4024_, v_i_4025_);
v___x_4030_ = lean_name_eq(v_k_4026_, v_k_x27_4029_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_unsigned_to_nat(1u);
v___x_4032_ = lean_nat_add(v_i_4025_, v___x_4031_);
lean_dec(v_i_4025_);
v_i_4025_ = v___x_4032_;
goto _start;
}
else
{
lean_dec(v_i_4025_);
return v___x_4030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4034_, lean_object* v_i_4035_, lean_object* v_k_4036_){
_start:
{
uint8_t v_res_4037_; lean_object* v_r_4038_; 
v_res_4037_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4034_, v_i_4035_, v_k_4036_);
lean_dec(v_k_4036_);
lean_dec_ref(v_keys_4034_);
v_r_4038_ = lean_box(v_res_4037_);
return v_r_4038_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4039_, size_t v_x_4040_, lean_object* v_x_4041_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
lean_object* v_es_4042_; lean_object* v___x_4043_; size_t v___x_4044_; size_t v___x_4045_; size_t v___x_4046_; lean_object* v_j_4047_; lean_object* v___x_4048_; 
v_es_4042_ = lean_ctor_get(v_x_4039_, 0);
v___x_4043_ = lean_box(2);
v___x_4044_ = ((size_t)5ULL);
v___x_4045_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4046_ = lean_usize_land(v_x_4040_, v___x_4045_);
v_j_4047_ = lean_usize_to_nat(v___x_4046_);
v___x_4048_ = lean_array_get_borrowed(v___x_4043_, v_es_4042_, v_j_4047_);
lean_dec(v_j_4047_);
switch(lean_obj_tag(v___x_4048_))
{
case 0:
{
lean_object* v_key_4049_; uint8_t v___x_4050_; 
v_key_4049_ = lean_ctor_get(v___x_4048_, 0);
v___x_4050_ = lean_name_eq(v_x_4041_, v_key_4049_);
return v___x_4050_;
}
case 1:
{
lean_object* v_node_4051_; size_t v___x_4052_; 
v_node_4051_ = lean_ctor_get(v___x_4048_, 0);
v___x_4052_ = lean_usize_shift_right(v_x_4040_, v___x_4044_);
v_x_4039_ = v_node_4051_;
v_x_4040_ = v___x_4052_;
goto _start;
}
default: 
{
uint8_t v___x_4054_; 
v___x_4054_ = 0;
return v___x_4054_;
}
}
}
else
{
lean_object* v_ks_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_ks_4055_ = lean_ctor_get(v_x_4039_, 0);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4055_, v___x_4056_, v_x_4041_);
return v___x_4057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4058_, lean_object* v_x_4059_, lean_object* v_x_4060_){
_start:
{
size_t v_x_2353__boxed_4061_; uint8_t v_res_4062_; lean_object* v_r_4063_; 
v_x_2353__boxed_4061_ = lean_unbox_usize(v_x_4059_);
lean_dec(v_x_4059_);
v_res_4062_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4058_, v_x_2353__boxed_4061_, v_x_4060_);
lean_dec(v_x_4060_);
lean_dec_ref(v_x_4058_);
v_r_4063_ = lean_box(v_res_4062_);
return v_r_4063_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4064_, lean_object* v_x_4065_){
_start:
{
uint64_t v___y_4067_; 
if (lean_obj_tag(v_x_4065_) == 0)
{
uint64_t v___x_4070_; 
v___x_4070_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4067_ = v___x_4070_;
goto v___jp_4066_;
}
else
{
uint64_t v_hash_4071_; 
v_hash_4071_ = lean_ctor_get_uint64(v_x_4065_, sizeof(void*)*2);
v___y_4067_ = v_hash_4071_;
goto v___jp_4066_;
}
v___jp_4066_:
{
size_t v___x_4068_; uint8_t v___x_4069_; 
v___x_4068_ = lean_uint64_to_usize(v___y_4067_);
v___x_4069_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4064_, v___x_4068_, v_x_4065_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4072_, lean_object* v_x_4073_){
_start:
{
uint8_t v_res_4074_; lean_object* v_r_4075_; 
v_res_4074_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4072_, v_x_4073_);
lean_dec(v_x_4073_);
lean_dec_ref(v_x_4072_);
v_r_4075_ = lean_box(v_res_4074_);
return v_r_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4076_, lean_object* v_declName_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_instanceNames_4084_; uint8_t v___x_4085_; 
v_instanceNames_4084_ = lean_ctor_get(v_d_4076_, 1);
v___x_4085_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4084_, v_declName_4077_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v_d_4076_);
v___x_4086_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4087_ = l_Lean_MessageData_ofConstName(v_declName_4077_, v___x_4085_);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4090_, v___y_4078_, v___y_4079_);
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
else
{
goto v___jp_4081_;
}
v___jp_4081_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = l_Lean_Meta_Instances_eraseCore(v_d_4076_, v_declName_4077_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4100_, lean_object* v_declName_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4100_, v_declName_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4106_, lean_object* v_declName_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; lean_object* v_env_4112_; lean_object* v___x_4113_; lean_object* v_ext_4114_; lean_object* v_toEnvExtension_4115_; lean_object* v_asyncMode_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4111_ = lean_st_ref_get(v___y_4109_);
v_env_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_env_4112_);
lean_dec(v___x_4111_);
v___x_4113_ = l_Lean_Meta_instanceExtension;
v_ext_4114_ = lean_ctor_get(v___x_4113_, 1);
v_toEnvExtension_4115_ = lean_ctor_get(v_ext_4114_, 0);
v_asyncMode_4116_ = lean_ctor_get(v_toEnvExtension_4115_, 2);
v___x_4117_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4106_, v___x_4113_, v_env_4112_, v_asyncMode_4116_);
v___x_4118_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4117_, v_declName_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4148_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4148_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4148_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v_env_4124_; lean_object* v_nextMacroScope_4125_; lean_object* v_ngen_4126_; lean_object* v_auxDeclNGen_4127_; lean_object* v_traceState_4128_; lean_object* v_messages_4129_; lean_object* v_infoState_4130_; lean_object* v_snapshotTasks_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4146_; 
v___x_4123_ = lean_st_ref_take(v___y_4109_);
v_env_4124_ = lean_ctor_get(v___x_4123_, 0);
v_nextMacroScope_4125_ = lean_ctor_get(v___x_4123_, 1);
v_ngen_4126_ = lean_ctor_get(v___x_4123_, 2);
v_auxDeclNGen_4127_ = lean_ctor_get(v___x_4123_, 3);
v_traceState_4128_ = lean_ctor_get(v___x_4123_, 4);
v_messages_4129_ = lean_ctor_get(v___x_4123_, 6);
v_infoState_4130_ = lean_ctor_get(v___x_4123_, 7);
v_snapshotTasks_4131_ = lean_ctor_get(v___x_4123_, 8);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v___x_4123_, 5);
lean_dec(v_unused_4147_);
v___x_4133_ = v___x_4123_;
v_isShared_4134_ = v_isSharedCheck_4146_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_snapshotTasks_4131_);
lean_inc(v_infoState_4130_);
lean_inc(v_messages_4129_);
lean_inc(v_traceState_4128_);
lean_inc(v_auxDeclNGen_4127_);
lean_inc(v_ngen_4126_);
lean_inc(v_nextMacroScope_4125_);
lean_inc(v_env_4124_);
lean_dec(v___x_4123_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4146_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___f_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___f_4135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4135_, 0, v_a_4119_);
v___x_4136_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4113_, v_env_4124_, v___f_4135_);
v___x_4137_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 5, v___x_4137_);
lean_ctor_set(v___x_4133_, 0, v___x_4136_);
v___x_4139_ = v___x_4133_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_nextMacroScope_4125_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_ngen_4126_);
lean_ctor_set(v_reuseFailAlloc_4145_, 3, v_auxDeclNGen_4127_);
lean_ctor_set(v_reuseFailAlloc_4145_, 4, v_traceState_4128_);
lean_ctor_set(v_reuseFailAlloc_4145_, 5, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4145_, 6, v_messages_4129_);
lean_ctor_set(v_reuseFailAlloc_4145_, 7, v_infoState_4130_);
lean_ctor_set(v_reuseFailAlloc_4145_, 8, v_snapshotTasks_4131_);
v___x_4139_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4140_ = lean_st_ref_set(v___y_4109_, v___x_4139_);
v___x_4141_ = lean_box(0);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4141_);
v___x_4143_ = v___x_4121_;
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
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4118_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4118_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4157_, lean_object* v_declName_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4157_, v_declName_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec_ref(v___x_4157_);
return v_res_4162_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4169_; uint64_t v___x_4170_; 
v___x_4169_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4170_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4169_);
return v___x_4170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4171_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4172_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set_uint64(v___x_4173_, sizeof(void*)*1, v___x_4171_);
return v___x_4173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4178_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
lean_ctor_set(v___x_4178_, 2, v___x_4177_);
lean_ctor_set(v___x_4178_, 3, v___x_4177_);
lean_ctor_set(v___x_4178_, 4, v___x_4177_);
lean_ctor_set(v___x_4178_, 5, v___x_4177_);
return v___x_4178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
lean_ctor_set(v___x_4180_, 2, v___x_4179_);
lean_ctor_set(v___x_4180_, 3, v___x_4179_);
lean_ctor_set(v___x_4180_, 4, v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v_declName_4183_, lean_object* v_stx_4184_, uint8_t v_attrKind_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = l_Lean_Syntax_getArg(v_stx_4184_, v___x_4189_);
v___x_4191_ = l_Lean_getAttrParamOptPrio(v___x_4190_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; uint8_t v___x_4193_; uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = 0;
v___x_4194_ = 1;
v___x_4195_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4196_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4197_ = lean_unsigned_to_nat(32u);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4197_);
v___x_4199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4200_ = ((size_t)5ULL);
lean_inc_n(v___x_4181_, 6);
v___x_4201_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4198_);
lean_ctor_set(v___x_4201_, 2, v___x_4181_);
lean_ctor_set(v___x_4201_, 3, v___x_4181_);
lean_ctor_set_usize(v___x_4201_, 4, v___x_4200_);
v___x_4202_ = lean_box(1);
lean_inc_ref(v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4196_);
lean_ctor_set(v___x_4203_, 1, v___x_4201_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
v___x_4204_ = lean_mk_empty_array_with_capacity(v___x_4181_);
v___x_4205_ = lean_box(0);
lean_inc(v___x_4182_);
v___x_4206_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4206_, 0, v___x_4195_);
lean_ctor_set(v___x_4206_, 1, v___x_4182_);
lean_ctor_set(v___x_4206_, 2, v___x_4203_);
lean_ctor_set(v___x_4206_, 3, v___x_4204_);
lean_ctor_set(v___x_4206_, 4, v___x_4205_);
lean_ctor_set(v___x_4206_, 5, v___x_4181_);
lean_ctor_set(v___x_4206_, 6, v___x_4205_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7, v___x_4193_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 1, v___x_4193_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 2, v___x_4193_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 3, v___x_4194_);
v___x_4207_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4181_);
lean_ctor_set(v___x_4207_, 1, v___x_4181_);
lean_ctor_set(v___x_4207_, 2, v___x_4181_);
lean_ctor_set(v___x_4207_, 3, v___x_4181_);
lean_ctor_set(v___x_4207_, 4, v___x_4196_);
lean_ctor_set(v___x_4207_, 5, v___x_4196_);
lean_ctor_set(v___x_4207_, 6, v___x_4196_);
lean_ctor_set(v___x_4207_, 7, v___x_4196_);
lean_ctor_set(v___x_4207_, 8, v___x_4196_);
lean_ctor_set(v___x_4207_, 9, v___x_4196_);
v___x_4208_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4209_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4207_);
lean_ctor_set(v___x_4210_, 1, v___x_4208_);
lean_ctor_set(v___x_4210_, 2, v___x_4182_);
lean_ctor_set(v___x_4210_, 3, v___x_4201_);
lean_ctor_set(v___x_4210_, 4, v___x_4209_);
v___x_4211_ = lean_st_mk_ref(v___x_4210_);
v___x_4212_ = l_Lean_Meta_addInstance(v_declName_4183_, v_attrKind_4185_, v_a_4192_, v___x_4206_, v___x_4211_, v___y_4186_, v___y_4187_);
lean_dec_ref(v___x_4206_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4221_; 
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v___x_4212_, 0);
lean_dec(v_unused_4222_);
v___x_4214_ = v___x_4212_;
v_isShared_4215_ = v_isSharedCheck_4221_;
goto v_resetjp_4213_;
}
else
{
lean_dec(v___x_4212_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4221_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4216_ = lean_st_ref_get(v___x_4211_);
lean_dec(v___x_4211_);
lean_dec(v___x_4216_);
v___x_4217_ = lean_box(0);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4217_);
v___x_4219_ = v___x_4214_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
else
{
lean_dec(v___x_4211_);
return v___x_4212_;
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_declName_4183_);
lean_dec(v___x_4182_);
lean_dec(v___x_4181_);
v_a_4223_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4191_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4191_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v_declName_4233_, lean_object* v_stx_4234_, lean_object* v_attrKind_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v_attrKind_boxed_4239_; lean_object* v_res_4240_; 
v_attrKind_boxed_4239_ = lean_unbox(v_attrKind_4235_);
v_res_4240_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4231_, v___x_4232_, v_declName_4233_, v_stx_4234_, v_attrKind_boxed_4239_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v_stx_4234_);
return v_res_4240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4241_; lean_object* v___f_4242_; 
v___x_4241_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4242_, 0, v___x_4241_);
return v___f_4242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4309_; lean_object* v___f_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___f_4309_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4310_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4311_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
lean_ctor_set(v___x_4312_, 1, v___f_4310_);
lean_ctor_set(v___x_4312_, 2, v___f_4309_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4315_ = l_Lean_registerBuiltinAttribute(v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4319_, v_x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4322_, lean_object* v_x_4323_, lean_object* v_x_4324_){
_start:
{
uint8_t v_res_4325_; lean_object* v_r_4326_; 
v_res_4325_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4322_, v_x_4323_, v_x_4324_);
lean_dec(v_x_4324_);
lean_dec_ref(v_x_4323_);
v_r_4326_ = lean_box(v_res_4325_);
return v_r_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4327_, lean_object* v_msg_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4328_, v___y_4329_, v___y_4330_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_msg_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4333_, v_msg_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4338_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4339_, lean_object* v_x_4340_, size_t v_x_4341_, lean_object* v_x_4342_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4340_, v_x_4341_, v_x_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4344_, lean_object* v_x_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_){
_start:
{
size_t v_x_3005__boxed_4348_; uint8_t v_res_4349_; lean_object* v_r_4350_; 
v_x_3005__boxed_4348_ = lean_unbox_usize(v_x_4346_);
lean_dec(v_x_4346_);
v_res_4349_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4344_, v_x_4345_, v_x_3005__boxed_4348_, v_x_4347_);
lean_dec(v_x_4347_);
lean_dec_ref(v_x_4345_);
v_r_4350_ = lean_box(v_res_4349_);
return v_r_4350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4351_, lean_object* v_keys_4352_, lean_object* v_vals_4353_, lean_object* v_heq_4354_, lean_object* v_i_4355_, lean_object* v_k_4356_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4352_, v_i_4355_, v_k_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4358_, lean_object* v_keys_4359_, lean_object* v_vals_4360_, lean_object* v_heq_4361_, lean_object* v_i_4362_, lean_object* v_k_4363_){
_start:
{
uint8_t v_res_4364_; lean_object* v_r_4365_; 
v_res_4364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4358_, v_keys_4359_, v_vals_4360_, v_heq_4361_, v_i_4362_, v_k_4363_);
lean_dec(v_k_4363_);
lean_dec_ref(v_vals_4360_);
lean_dec_ref(v_keys_4359_);
v_r_4365_ = lean_box(v_res_4364_);
return v_r_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4370_ = l_Lean_addBuiltinDocString(v___x_4368_, v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4373_){
_start:
{
lean_object* v___x_4375_; lean_object* v_env_4376_; lean_object* v___x_4377_; lean_object* v_ext_4378_; lean_object* v_toEnvExtension_4379_; lean_object* v_asyncMode_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v_discrTree_4383_; lean_object* v___x_4384_; 
v___x_4375_ = lean_st_ref_get(v_a_4373_);
v_env_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc_ref(v_env_4376_);
lean_dec(v___x_4375_);
v___x_4377_ = l_Lean_Meta_instanceExtension;
v_ext_4378_ = lean_ctor_get(v___x_4377_, 1);
v_toEnvExtension_4379_ = lean_ctor_get(v_ext_4378_, 0);
v_asyncMode_4380_ = lean_ctor_get(v_toEnvExtension_4379_, 2);
v___x_4381_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4382_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4381_, v___x_4377_, v_env_4376_, v_asyncMode_4380_);
v_discrTree_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc_ref(v_discrTree_4383_);
lean_dec(v___x_4382_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v_discrTree_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4385_);
lean_dec(v_a_4385_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v_env_4399_; lean_object* v___x_4400_; lean_object* v_ext_4401_; lean_object* v_toEnvExtension_4402_; lean_object* v_asyncMode_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v_erased_4406_; lean_object* v___x_4407_; 
v___x_4398_ = lean_st_ref_get(v_a_4396_);
v_env_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_ref(v_env_4399_);
lean_dec(v___x_4398_);
v___x_4400_ = l_Lean_Meta_instanceExtension;
v_ext_4401_ = lean_ctor_get(v___x_4400_, 1);
v_toEnvExtension_4402_ = lean_ctor_get(v_ext_4401_, 0);
v_asyncMode_4403_ = lean_ctor_get(v_toEnvExtension_4402_, 2);
v___x_4404_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4405_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4404_, v___x_4400_, v_env_4399_, v_asyncMode_4403_);
v_erased_4406_ = lean_ctor_get(v___x_4405_, 2);
lean_inc_ref(v_erased_4406_);
lean_dec(v___x_4405_);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v_erased_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4408_);
lean_dec(v_a_4408_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_Meta_getErasedInstances(v_a_4415_, v_a_4416_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4419_, lean_object* v_declName_4420_){
_start:
{
lean_object* v___x_4421_; lean_object* v_ext_4422_; lean_object* v_toEnvExtension_4423_; lean_object* v_asyncMode_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v_instanceNames_4427_; uint8_t v___x_4428_; 
v___x_4421_ = l_Lean_Meta_instanceExtension;
v_ext_4422_ = lean_ctor_get(v___x_4421_, 1);
v_toEnvExtension_4423_ = lean_ctor_get(v_ext_4422_, 0);
v_asyncMode_4424_ = lean_ctor_get(v_toEnvExtension_4423_, 2);
v___x_4425_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4426_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4425_, v___x_4421_, v_env_4419_, v_asyncMode_4424_);
v_instanceNames_4427_ = lean_ctor_get(v___x_4426_, 1);
lean_inc_ref(v_instanceNames_4427_);
lean_dec(v___x_4426_);
v___x_4428_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4427_, v_declName_4420_);
lean_dec_ref(v_instanceNames_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4429_, lean_object* v_declName_4430_){
_start:
{
uint8_t v_res_4431_; lean_object* v_r_4432_; 
v_res_4431_ = l_Lean_Meta_isInstanceCore(v_env_4429_, v_declName_4430_);
lean_dec(v_declName_4430_);
v_r_4432_ = lean_box(v_res_4431_);
return v_r_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; lean_object* v_env_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4436_ = lean_st_ref_get(v_a_4434_);
v_env_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc_ref(v_env_4437_);
lean_dec(v___x_4436_);
v___x_4438_ = l_Lean_Meta_isInstanceCore(v_env_4437_, v_declName_4433_);
v___x_4439_ = lean_box(v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_Meta_isInstance___redArg(v_declName_4441_, v_a_4442_);
lean_dec(v_a_4442_);
lean_dec(v_declName_4441_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Meta_isInstance___redArg(v_declName_4445_, v_a_4447_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Meta_isInstance(v_declName_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_declName_4450_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4455_, lean_object* v_vals_4456_, lean_object* v_i_4457_, lean_object* v_k_4458_){
_start:
{
lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4459_ = lean_array_get_size(v_keys_4455_);
v___x_4460_ = lean_nat_dec_lt(v_i_4457_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
lean_dec(v_i_4457_);
v___x_4461_ = lean_box(0);
return v___x_4461_;
}
else
{
lean_object* v_k_x27_4462_; uint8_t v___x_4463_; 
v_k_x27_4462_ = lean_array_fget_borrowed(v_keys_4455_, v_i_4457_);
v___x_4463_ = lean_name_eq(v_k_4458_, v_k_x27_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4464_ = lean_unsigned_to_nat(1u);
v___x_4465_ = lean_nat_add(v_i_4457_, v___x_4464_);
lean_dec(v_i_4457_);
v_i_4457_ = v___x_4465_;
goto _start;
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_array_fget_borrowed(v_vals_4456_, v_i_4457_);
lean_dec(v_i_4457_);
lean_inc(v___x_4467_);
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4469_, lean_object* v_vals_4470_, lean_object* v_i_4471_, lean_object* v_k_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4469_, v_vals_4470_, v_i_4471_, v_k_4472_);
lean_dec(v_k_4472_);
lean_dec_ref(v_vals_4470_);
lean_dec_ref(v_keys_4469_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4474_, size_t v_x_4475_, lean_object* v_x_4476_){
_start:
{
if (lean_obj_tag(v_x_4474_) == 0)
{
lean_object* v_es_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4498_; 
v_es_4477_ = lean_ctor_get(v_x_4474_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_x_4474_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4479_ = v_x_4474_;
v_isShared_4480_ = v_isSharedCheck_4498_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_es_4477_);
lean_dec(v_x_4474_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4498_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; size_t v___x_4482_; size_t v___x_4483_; size_t v___x_4484_; lean_object* v_j_4485_; lean_object* v___x_4486_; 
v___x_4481_ = lean_box(2);
v___x_4482_ = ((size_t)5ULL);
v___x_4483_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4484_ = lean_usize_land(v_x_4475_, v___x_4483_);
v_j_4485_ = lean_usize_to_nat(v___x_4484_);
v___x_4486_ = lean_array_get(v___x_4481_, v_es_4477_, v_j_4485_);
lean_dec(v_j_4485_);
lean_dec_ref(v_es_4477_);
switch(lean_obj_tag(v___x_4486_))
{
case 0:
{
lean_object* v_key_4487_; lean_object* v_val_4488_; uint8_t v___x_4489_; 
v_key_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_key_4487_);
v_val_4488_ = lean_ctor_get(v___x_4486_, 1);
lean_inc(v_val_4488_);
lean_dec_ref(v___x_4486_);
v___x_4489_ = lean_name_eq(v_x_4476_, v_key_4487_);
lean_dec(v_key_4487_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
lean_dec(v_val_4488_);
lean_del_object(v___x_4479_);
v___x_4490_ = lean_box(0);
return v___x_4490_;
}
else
{
lean_object* v___x_4492_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set_tag(v___x_4479_, 1);
lean_ctor_set(v___x_4479_, 0, v_val_4488_);
v___x_4492_ = v___x_4479_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_val_4488_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
case 1:
{
lean_object* v_node_4494_; size_t v___x_4495_; 
lean_del_object(v___x_4479_);
v_node_4494_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_node_4494_);
lean_dec_ref(v___x_4486_);
v___x_4495_ = lean_usize_shift_right(v_x_4475_, v___x_4482_);
v_x_4474_ = v_node_4494_;
v_x_4475_ = v___x_4495_;
goto _start;
}
default: 
{
lean_object* v___x_4497_; 
lean_del_object(v___x_4479_);
v___x_4497_ = lean_box(0);
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_ks_4499_; lean_object* v_vs_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v_ks_4499_ = lean_ctor_get(v_x_4474_, 0);
lean_inc_ref(v_ks_4499_);
v_vs_4500_ = lean_ctor_get(v_x_4474_, 1);
lean_inc_ref(v_vs_4500_);
lean_dec_ref(v_x_4474_);
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4499_, v_vs_4500_, v___x_4501_, v_x_4476_);
lean_dec_ref(v_vs_4500_);
lean_dec_ref(v_ks_4499_);
return v___x_4502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4503_, lean_object* v_x_4504_, lean_object* v_x_4505_){
_start:
{
size_t v_x_489__boxed_4506_; lean_object* v_res_4507_; 
v_x_489__boxed_4506_ = lean_unbox_usize(v_x_4504_);
lean_dec(v_x_4504_);
v_res_4507_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4503_, v_x_489__boxed_4506_, v_x_4505_);
lean_dec(v_x_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4508_, lean_object* v_x_4509_){
_start:
{
uint64_t v___y_4511_; 
if (lean_obj_tag(v_x_4509_) == 0)
{
uint64_t v___x_4514_; 
v___x_4514_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4511_ = v___x_4514_;
goto v___jp_4510_;
}
else
{
uint64_t v_hash_4515_; 
v_hash_4515_ = lean_ctor_get_uint64(v_x_4509_, sizeof(void*)*2);
v___y_4511_ = v_hash_4515_;
goto v___jp_4510_;
}
v___jp_4510_:
{
size_t v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = lean_uint64_to_usize(v___y_4511_);
v___x_4513_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4508_, v___x_4512_, v_x_4509_);
return v___x_4513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4516_, lean_object* v_x_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4516_, v_x_4517_);
lean_dec(v_x_4517_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v_env_4523_; lean_object* v___x_4524_; lean_object* v_ext_4525_; lean_object* v_toEnvExtension_4526_; lean_object* v_asyncMode_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v_instanceNames_4530_; lean_object* v___x_4531_; 
v___x_4522_ = lean_st_ref_get(v_a_4520_);
v_env_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc_ref(v_env_4523_);
lean_dec(v___x_4522_);
v___x_4524_ = l_Lean_Meta_instanceExtension;
v_ext_4525_ = lean_ctor_get(v___x_4524_, 1);
v_toEnvExtension_4526_ = lean_ctor_get(v_ext_4525_, 0);
v_asyncMode_4527_ = lean_ctor_get(v_toEnvExtension_4526_, 2);
v___x_4528_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4529_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4528_, v___x_4524_, v_env_4523_, v_asyncMode_4527_);
v_instanceNames_4530_ = lean_ctor_get(v___x_4529_, 1);
lean_inc_ref(v_instanceNames_4530_);
lean_dec(v___x_4529_);
v___x_4531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4530_, v_declName_4519_);
if (lean_obj_tag(v___x_4531_) == 1)
{
lean_object* v_val_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4541_; 
v_val_4532_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4534_ = v___x_4531_;
v_isShared_4535_ = v_isSharedCheck_4541_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_val_4532_);
lean_dec(v___x_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4541_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v_priority_4536_; lean_object* v___x_4538_; 
v_priority_4536_ = lean_ctor_get(v_val_4532_, 2);
lean_inc(v_priority_4536_);
lean_dec(v_val_4532_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v_priority_4536_);
v___x_4538_ = v___x_4534_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_priority_4536_);
v___x_4538_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
return v___x_4539_;
}
}
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec(v___x_4531_);
v___x_4542_ = lean_box(0);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec(v_declName_4544_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4548_, v_a_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4553_, v_a_4554_, v_a_4555_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_declName_4553_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4558_, lean_object* v_x_4559_, lean_object* v_x_4560_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4559_, v_x_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4562_, lean_object* v_x_4563_, lean_object* v_x_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4562_, v_x_4563_, v_x_4564_);
lean_dec(v_x_4564_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4566_, lean_object* v_x_4567_, size_t v_x_4568_, lean_object* v_x_4569_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4567_, v_x_4568_, v_x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4571_, lean_object* v_x_4572_, lean_object* v_x_4573_, lean_object* v_x_4574_){
_start:
{
size_t v_x_617__boxed_4575_; lean_object* v_res_4576_; 
v_x_617__boxed_4575_ = lean_unbox_usize(v_x_4573_);
lean_dec(v_x_4573_);
v_res_4576_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4571_, v_x_4572_, v_x_617__boxed_4575_, v_x_4574_);
lean_dec(v_x_4574_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4577_, lean_object* v_keys_4578_, lean_object* v_vals_4579_, lean_object* v_heq_4580_, lean_object* v_i_4581_, lean_object* v_k_4582_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4578_, v_vals_4579_, v_i_4581_, v_k_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4584_, lean_object* v_keys_4585_, lean_object* v_vals_4586_, lean_object* v_heq_4587_, lean_object* v_i_4588_, lean_object* v_k_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4584_, v_keys_4585_, v_vals_4586_, v_heq_4587_, v_i_4588_, v_k_4589_);
lean_dec(v_k_4589_);
lean_dec_ref(v_vals_4586_);
lean_dec_ref(v_keys_4585_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v_env_4595_; lean_object* v___x_4596_; lean_object* v_ext_4597_; lean_object* v_toEnvExtension_4598_; lean_object* v_asyncMode_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v_instanceNames_4602_; lean_object* v___x_4603_; 
v___x_4594_ = lean_st_ref_get(v_a_4592_);
v_env_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc_ref(v_env_4595_);
lean_dec(v___x_4594_);
v___x_4596_ = l_Lean_Meta_instanceExtension;
v_ext_4597_ = lean_ctor_get(v___x_4596_, 1);
v_toEnvExtension_4598_ = lean_ctor_get(v_ext_4597_, 0);
v_asyncMode_4599_ = lean_ctor_get(v_toEnvExtension_4598_, 2);
v___x_4600_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4601_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4600_, v___x_4596_, v_env_4595_, v_asyncMode_4599_);
v_instanceNames_4602_ = lean_ctor_get(v___x_4601_, 1);
lean_inc_ref(v_instanceNames_4602_);
lean_dec(v___x_4601_);
v___x_4603_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4602_, v_declName_4591_);
if (lean_obj_tag(v___x_4603_) == 1)
{
lean_object* v_val_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4614_; 
v_val_4604_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4606_ = v___x_4603_;
v_isShared_4607_ = v_isSharedCheck_4614_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_val_4604_);
lean_dec(v___x_4603_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4614_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
uint8_t v_attrKind_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v_attrKind_4608_ = lean_ctor_get_uint8(v_val_4604_, sizeof(void*)*5);
lean_dec(v_val_4604_);
v___x_4609_ = lean_box(v_attrKind_4608_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4609_);
v___x_4611_ = v___x_4606_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; 
v___x_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
return v___x_4612_;
}
}
}
else
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
lean_dec(v___x_4603_);
v___x_4615_ = lean_box(0);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec(v_declName_4617_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4621_, v_a_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4626_, v_a_4627_, v_a_4628_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_declName_4626_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_4635_, lean_object* v_v_4636_, lean_object* v_t_4637_){
_start:
{
if (lean_obj_tag(v_t_4637_) == 0)
{
lean_object* v_size_4638_; lean_object* v_k_4639_; lean_object* v_v_4640_; lean_object* v_l_4641_; lean_object* v_r_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4923_; 
v_size_4638_ = lean_ctor_get(v_t_4637_, 0);
v_k_4639_ = lean_ctor_get(v_t_4637_, 1);
v_v_4640_ = lean_ctor_get(v_t_4637_, 2);
v_l_4641_ = lean_ctor_get(v_t_4637_, 3);
v_r_4642_ = lean_ctor_get(v_t_4637_, 4);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_t_4637_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4644_ = v_t_4637_;
v_isShared_4645_ = v_isSharedCheck_4923_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_r_4642_);
lean_inc(v_l_4641_);
lean_inc(v_v_4640_);
lean_inc(v_k_4639_);
lean_inc(v_size_4638_);
lean_dec(v_t_4637_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4923_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
uint8_t v___x_4646_; 
v___x_4646_ = lean_nat_dec_lt(v_k_4639_, v_k_4635_);
if (v___x_4646_ == 0)
{
uint8_t v___x_4647_; 
v___x_4647_ = lean_nat_dec_eq(v_k_4639_, v_k_4635_);
if (v___x_4647_ == 0)
{
lean_object* v_impl_4648_; lean_object* v___x_4649_; 
lean_dec(v_size_4638_);
v_impl_4648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4635_, v_v_4636_, v_r_4642_);
v___x_4649_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4641_) == 0)
{
lean_object* v_size_4650_; lean_object* v_size_4651_; lean_object* v_k_4652_; lean_object* v_v_4653_; lean_object* v_l_4654_; lean_object* v_r_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v_size_4650_ = lean_ctor_get(v_l_4641_, 0);
v_size_4651_ = lean_ctor_get(v_impl_4648_, 0);
lean_inc(v_size_4651_);
v_k_4652_ = lean_ctor_get(v_impl_4648_, 1);
lean_inc(v_k_4652_);
v_v_4653_ = lean_ctor_get(v_impl_4648_, 2);
lean_inc(v_v_4653_);
v_l_4654_ = lean_ctor_get(v_impl_4648_, 3);
lean_inc(v_l_4654_);
v_r_4655_ = lean_ctor_get(v_impl_4648_, 4);
lean_inc(v_r_4655_);
v___x_4656_ = lean_unsigned_to_nat(3u);
v___x_4657_ = lean_nat_mul(v___x_4656_, v_size_4650_);
v___x_4658_ = lean_nat_dec_lt(v___x_4657_, v_size_4651_);
lean_dec(v___x_4657_);
if (v___x_4658_ == 0)
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_dec(v_r_4655_);
lean_dec(v_l_4654_);
lean_dec(v_v_4653_);
lean_dec(v_k_4652_);
v___x_4659_ = lean_nat_add(v___x_4649_, v_size_4650_);
v___x_4660_ = lean_nat_add(v___x_4659_, v_size_4651_);
lean_dec(v_size_4651_);
lean_dec(v___x_4659_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_impl_4648_);
lean_ctor_set(v___x_4644_, 0, v___x_4660_);
v___x_4662_ = v___x_4644_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_l_4641_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_impl_4648_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
else
{
lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4727_; 
v_isSharedCheck_4727_ = !lean_is_exclusive(v_impl_4648_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; lean_object* v_unused_4729_; lean_object* v_unused_4730_; lean_object* v_unused_4731_; lean_object* v_unused_4732_; 
v_unused_4728_ = lean_ctor_get(v_impl_4648_, 4);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_impl_4648_, 3);
lean_dec(v_unused_4729_);
v_unused_4730_ = lean_ctor_get(v_impl_4648_, 2);
lean_dec(v_unused_4730_);
v_unused_4731_ = lean_ctor_get(v_impl_4648_, 1);
lean_dec(v_unused_4731_);
v_unused_4732_ = lean_ctor_get(v_impl_4648_, 0);
lean_dec(v_unused_4732_);
v___x_4665_ = v_impl_4648_;
v_isShared_4666_ = v_isSharedCheck_4727_;
goto v_resetjp_4664_;
}
else
{
lean_dec(v_impl_4648_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4727_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v_size_4667_; lean_object* v_k_4668_; lean_object* v_v_4669_; lean_object* v_l_4670_; lean_object* v_r_4671_; lean_object* v_size_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v_size_4667_ = lean_ctor_get(v_l_4654_, 0);
v_k_4668_ = lean_ctor_get(v_l_4654_, 1);
v_v_4669_ = lean_ctor_get(v_l_4654_, 2);
v_l_4670_ = lean_ctor_get(v_l_4654_, 3);
v_r_4671_ = lean_ctor_get(v_l_4654_, 4);
v_size_4672_ = lean_ctor_get(v_r_4655_, 0);
v___x_4673_ = lean_unsigned_to_nat(2u);
v___x_4674_ = lean_nat_mul(v___x_4673_, v_size_4672_);
v___x_4675_ = lean_nat_dec_lt(v_size_4667_, v___x_4674_);
lean_dec(v___x_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4703_; 
lean_inc(v_r_4671_);
lean_inc(v_l_4670_);
lean_inc(v_v_4669_);
lean_inc(v_k_4668_);
v_isSharedCheck_4703_ = !lean_is_exclusive(v_l_4654_);
if (v_isSharedCheck_4703_ == 0)
{
lean_object* v_unused_4704_; lean_object* v_unused_4705_; lean_object* v_unused_4706_; lean_object* v_unused_4707_; lean_object* v_unused_4708_; 
v_unused_4704_ = lean_ctor_get(v_l_4654_, 4);
lean_dec(v_unused_4704_);
v_unused_4705_ = lean_ctor_get(v_l_4654_, 3);
lean_dec(v_unused_4705_);
v_unused_4706_ = lean_ctor_get(v_l_4654_, 2);
lean_dec(v_unused_4706_);
v_unused_4707_ = lean_ctor_get(v_l_4654_, 1);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_l_4654_, 0);
lean_dec(v_unused_4708_);
v___x_4677_ = v_l_4654_;
v_isShared_4678_ = v_isSharedCheck_4703_;
goto v_resetjp_4676_;
}
else
{
lean_dec(v_l_4654_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4703_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4693_; 
v___x_4679_ = lean_nat_add(v___x_4649_, v_size_4650_);
v___x_4680_ = lean_nat_add(v___x_4679_, v_size_4651_);
lean_dec(v_size_4651_);
if (lean_obj_tag(v_l_4670_) == 0)
{
lean_object* v_size_4701_; 
v_size_4701_ = lean_ctor_get(v_l_4670_, 0);
lean_inc(v_size_4701_);
v___y_4693_ = v_size_4701_;
goto v___jp_4692_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___y_4693_ = v___x_4702_;
goto v___jp_4692_;
}
v___jp_4681_:
{
lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4685_ = lean_nat_add(v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec(v___y_4683_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_r_4655_);
lean_ctor_set(v___x_4677_, 3, v_r_4671_);
lean_ctor_set(v___x_4677_, 2, v_v_4653_);
lean_ctor_set(v___x_4677_, 1, v_k_4652_);
lean_ctor_set(v___x_4677_, 0, v___x_4685_);
v___x_4687_ = v___x_4677_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_k_4652_);
lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_v_4653_);
lean_ctor_set(v_reuseFailAlloc_4691_, 3, v_r_4671_);
lean_ctor_set(v_reuseFailAlloc_4691_, 4, v_r_4655_);
v___x_4687_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4689_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v___x_4687_);
lean_ctor_set(v___x_4665_, 3, v___y_4682_);
lean_ctor_set(v___x_4665_, 2, v_v_4669_);
lean_ctor_set(v___x_4665_, 1, v_k_4668_);
lean_ctor_set(v___x_4665_, 0, v___x_4680_);
v___x_4689_ = v___x_4665_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v_k_4668_);
lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_v_4669_);
lean_ctor_set(v_reuseFailAlloc_4690_, 3, v___y_4682_);
lean_ctor_set(v_reuseFailAlloc_4690_, 4, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
v___jp_4692_:
{
lean_object* v___x_4694_; lean_object* v___x_4696_; 
v___x_4694_ = lean_nat_add(v___x_4679_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec(v___x_4679_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_l_4670_);
lean_ctor_set(v___x_4644_, 0, v___x_4694_);
v___x_4696_ = v___x_4644_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4700_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4700_, 3, v_l_4641_);
lean_ctor_set(v_reuseFailAlloc_4700_, 4, v_l_4670_);
v___x_4696_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_nat_add(v___x_4649_, v_size_4672_);
if (lean_obj_tag(v_r_4671_) == 0)
{
lean_object* v_size_4698_; 
v_size_4698_ = lean_ctor_get(v_r_4671_, 0);
lean_inc(v_size_4698_);
v___y_4682_ = v___x_4696_;
v___y_4683_ = v___x_4697_;
v___y_4684_ = v_size_4698_;
goto v___jp_4681_;
}
else
{
lean_object* v___x_4699_; 
v___x_4699_ = lean_unsigned_to_nat(0u);
v___y_4682_ = v___x_4696_;
v___y_4683_ = v___x_4697_;
v___y_4684_ = v___x_4699_;
goto v___jp_4681_;
}
}
}
}
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4713_; 
lean_del_object(v___x_4644_);
v___x_4709_ = lean_nat_add(v___x_4649_, v_size_4650_);
v___x_4710_ = lean_nat_add(v___x_4709_, v_size_4651_);
lean_dec(v_size_4651_);
v___x_4711_ = lean_nat_add(v___x_4709_, v_size_4667_);
lean_dec(v___x_4709_);
lean_inc_ref(v_l_4641_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_l_4654_);
lean_ctor_set(v___x_4665_, 3, v_l_4641_);
lean_ctor_set(v___x_4665_, 2, v_v_4640_);
lean_ctor_set(v___x_4665_, 1, v_k_4639_);
lean_ctor_set(v___x_4665_, 0, v___x_4711_);
v___x_4713_ = v___x_4665_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4726_, 3, v_l_4641_);
lean_ctor_set(v_reuseFailAlloc_4726_, 4, v_l_4654_);
v___x_4713_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
v_isSharedCheck_4720_ = !lean_is_exclusive(v_l_4641_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; lean_object* v_unused_4722_; lean_object* v_unused_4723_; lean_object* v_unused_4724_; lean_object* v_unused_4725_; 
v_unused_4721_ = lean_ctor_get(v_l_4641_, 4);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_l_4641_, 3);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_l_4641_, 2);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_l_4641_, 1);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_l_4641_, 0);
lean_dec(v_unused_4725_);
v___x_4715_ = v_l_4641_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_dec(v_l_4641_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 4, v_r_4655_);
lean_ctor_set(v___x_4715_, 3, v___x_4713_);
lean_ctor_set(v___x_4715_, 2, v_v_4653_);
lean_ctor_set(v___x_4715_, 1, v_k_4652_);
lean_ctor_set(v___x_4715_, 0, v___x_4710_);
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_k_4652_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_v_4653_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4719_, 4, v_r_4655_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4733_; 
v_l_4733_ = lean_ctor_get(v_impl_4648_, 3);
lean_inc(v_l_4733_);
if (lean_obj_tag(v_l_4733_) == 0)
{
lean_object* v_r_4734_; lean_object* v_k_4735_; lean_object* v_v_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4759_; 
v_r_4734_ = lean_ctor_get(v_impl_4648_, 4);
v_k_4735_ = lean_ctor_get(v_impl_4648_, 1);
v_v_4736_ = lean_ctor_get(v_impl_4648_, 2);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_impl_4648_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; lean_object* v_unused_4761_; 
v_unused_4760_ = lean_ctor_get(v_impl_4648_, 3);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_impl_4648_, 0);
lean_dec(v_unused_4761_);
v___x_4738_ = v_impl_4648_;
v_isShared_4739_ = v_isSharedCheck_4759_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_r_4734_);
lean_inc(v_v_4736_);
lean_inc(v_k_4735_);
lean_dec(v_impl_4648_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4759_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v_k_4740_; lean_object* v_v_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4755_; 
v_k_4740_ = lean_ctor_get(v_l_4733_, 1);
v_v_4741_ = lean_ctor_get(v_l_4733_, 2);
v_isSharedCheck_4755_ = !lean_is_exclusive(v_l_4733_);
if (v_isSharedCheck_4755_ == 0)
{
lean_object* v_unused_4756_; lean_object* v_unused_4757_; lean_object* v_unused_4758_; 
v_unused_4756_ = lean_ctor_get(v_l_4733_, 4);
lean_dec(v_unused_4756_);
v_unused_4757_ = lean_ctor_get(v_l_4733_, 3);
lean_dec(v_unused_4757_);
v_unused_4758_ = lean_ctor_get(v_l_4733_, 0);
lean_dec(v_unused_4758_);
v___x_4743_ = v_l_4733_;
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_v_4741_);
lean_inc(v_k_4740_);
lean_dec(v_l_4733_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4745_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4734_, 2);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 4, v_r_4734_);
lean_ctor_set(v___x_4743_, 3, v_r_4734_);
lean_ctor_set(v___x_4743_, 2, v_v_4640_);
lean_ctor_set(v___x_4743_, 1, v_k_4639_);
lean_ctor_set(v___x_4743_, 0, v___x_4649_);
v___x_4747_ = v___x_4743_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_r_4734_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v_r_4734_);
v___x_4747_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
lean_inc(v_r_4734_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 3, v_r_4734_);
lean_ctor_set(v___x_4738_, 0, v___x_4649_);
v___x_4749_ = v___x_4738_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_k_4735_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_v_4736_);
lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_r_4734_);
lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_r_4734_);
v___x_4749_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4751_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v___x_4749_);
lean_ctor_set(v___x_4644_, 3, v___x_4747_);
lean_ctor_set(v___x_4644_, 2, v_v_4741_);
lean_ctor_set(v___x_4644_, 1, v_k_4740_);
lean_ctor_set(v___x_4644_, 0, v___x_4745_);
v___x_4751_ = v___x_4644_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4740_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4741_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
}
else
{
lean_object* v_r_4762_; 
v_r_4762_ = lean_ctor_get(v_impl_4648_, 4);
lean_inc(v_r_4762_);
if (lean_obj_tag(v_r_4762_) == 0)
{
lean_object* v_k_4763_; lean_object* v_v_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4775_; 
v_k_4763_ = lean_ctor_get(v_impl_4648_, 1);
v_v_4764_ = lean_ctor_get(v_impl_4648_, 2);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_impl_4648_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; lean_object* v_unused_4777_; lean_object* v_unused_4778_; 
v_unused_4776_ = lean_ctor_get(v_impl_4648_, 4);
lean_dec(v_unused_4776_);
v_unused_4777_ = lean_ctor_get(v_impl_4648_, 3);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_impl_4648_, 0);
lean_dec(v_unused_4778_);
v___x_4766_ = v_impl_4648_;
v_isShared_4767_ = v_isSharedCheck_4775_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_v_4764_);
lean_inc(v_k_4763_);
lean_dec(v_impl_4648_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4775_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4768_; lean_object* v___x_4770_; 
v___x_4768_ = lean_unsigned_to_nat(3u);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 4, v_l_4733_);
lean_ctor_set(v___x_4766_, 2, v_v_4640_);
lean_ctor_set(v___x_4766_, 1, v_k_4639_);
lean_ctor_set(v___x_4766_, 0, v___x_4649_);
v___x_4770_ = v___x_4766_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_l_4733_);
lean_ctor_set(v_reuseFailAlloc_4774_, 4, v_l_4733_);
v___x_4770_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4772_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_r_4762_);
lean_ctor_set(v___x_4644_, 3, v___x_4770_);
lean_ctor_set(v___x_4644_, 2, v_v_4764_);
lean_ctor_set(v___x_4644_, 1, v_k_4763_);
lean_ctor_set(v___x_4644_, 0, v___x_4768_);
v___x_4772_ = v___x_4644_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_k_4763_);
lean_ctor_set(v_reuseFailAlloc_4773_, 2, v_v_4764_);
lean_ctor_set(v_reuseFailAlloc_4773_, 3, v___x_4770_);
lean_ctor_set(v_reuseFailAlloc_4773_, 4, v_r_4762_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
else
{
lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4779_ = lean_unsigned_to_nat(2u);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_impl_4648_);
lean_ctor_set(v___x_4644_, 3, v_r_4762_);
lean_ctor_set(v___x_4644_, 0, v___x_4779_);
v___x_4781_ = v___x_4644_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_r_4762_);
lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_impl_4648_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
}
else
{
lean_object* v___x_4784_; 
lean_dec(v_v_4640_);
lean_dec(v_k_4639_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 2, v_v_4636_);
lean_ctor_set(v___x_4644_, 1, v_k_4635_);
v___x_4784_ = v___x_4644_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_size_4638_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_l_4641_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_r_4642_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
else
{
lean_object* v_impl_4786_; lean_object* v___x_4787_; 
lean_dec(v_size_4638_);
v_impl_4786_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4635_, v_v_4636_, v_l_4641_);
v___x_4787_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4642_) == 0)
{
lean_object* v_size_4788_; lean_object* v_size_4789_; lean_object* v_k_4790_; lean_object* v_v_4791_; lean_object* v_l_4792_; lean_object* v_r_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; 
v_size_4788_ = lean_ctor_get(v_r_4642_, 0);
v_size_4789_ = lean_ctor_get(v_impl_4786_, 0);
lean_inc(v_size_4789_);
v_k_4790_ = lean_ctor_get(v_impl_4786_, 1);
lean_inc(v_k_4790_);
v_v_4791_ = lean_ctor_get(v_impl_4786_, 2);
lean_inc(v_v_4791_);
v_l_4792_ = lean_ctor_get(v_impl_4786_, 3);
lean_inc(v_l_4792_);
v_r_4793_ = lean_ctor_get(v_impl_4786_, 4);
lean_inc(v_r_4793_);
v___x_4794_ = lean_unsigned_to_nat(3u);
v___x_4795_ = lean_nat_mul(v___x_4794_, v_size_4788_);
v___x_4796_ = lean_nat_dec_lt(v___x_4795_, v_size_4789_);
lean_dec(v___x_4795_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
lean_dec(v_r_4793_);
lean_dec(v_l_4792_);
lean_dec(v_v_4791_);
lean_dec(v_k_4790_);
v___x_4797_ = lean_nat_add(v___x_4787_, v_size_4789_);
lean_dec(v_size_4789_);
v___x_4798_ = lean_nat_add(v___x_4797_, v_size_4788_);
lean_dec(v___x_4797_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 3, v_impl_4786_);
lean_ctor_set(v___x_4644_, 0, v___x_4798_);
v___x_4800_ = v___x_4644_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4801_, 3, v_impl_4786_);
lean_ctor_set(v_reuseFailAlloc_4801_, 4, v_r_4642_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
else
{
lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4867_; 
v_isSharedCheck_4867_ = !lean_is_exclusive(v_impl_4786_);
if (v_isSharedCheck_4867_ == 0)
{
lean_object* v_unused_4868_; lean_object* v_unused_4869_; lean_object* v_unused_4870_; lean_object* v_unused_4871_; lean_object* v_unused_4872_; 
v_unused_4868_ = lean_ctor_get(v_impl_4786_, 4);
lean_dec(v_unused_4868_);
v_unused_4869_ = lean_ctor_get(v_impl_4786_, 3);
lean_dec(v_unused_4869_);
v_unused_4870_ = lean_ctor_get(v_impl_4786_, 2);
lean_dec(v_unused_4870_);
v_unused_4871_ = lean_ctor_get(v_impl_4786_, 1);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_impl_4786_, 0);
lean_dec(v_unused_4872_);
v___x_4803_ = v_impl_4786_;
v_isShared_4804_ = v_isSharedCheck_4867_;
goto v_resetjp_4802_;
}
else
{
lean_dec(v_impl_4786_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4867_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_size_4805_; lean_object* v_size_4806_; lean_object* v_k_4807_; lean_object* v_v_4808_; lean_object* v_l_4809_; lean_object* v_r_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v_size_4805_ = lean_ctor_get(v_l_4792_, 0);
v_size_4806_ = lean_ctor_get(v_r_4793_, 0);
v_k_4807_ = lean_ctor_get(v_r_4793_, 1);
v_v_4808_ = lean_ctor_get(v_r_4793_, 2);
v_l_4809_ = lean_ctor_get(v_r_4793_, 3);
v_r_4810_ = lean_ctor_get(v_r_4793_, 4);
v___x_4811_ = lean_unsigned_to_nat(2u);
v___x_4812_ = lean_nat_mul(v___x_4811_, v_size_4805_);
v___x_4813_ = lean_nat_dec_lt(v_size_4806_, v___x_4812_);
lean_dec(v___x_4812_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4842_; 
lean_inc(v_r_4810_);
lean_inc(v_l_4809_);
lean_inc(v_v_4808_);
lean_inc(v_k_4807_);
v_isSharedCheck_4842_ = !lean_is_exclusive(v_r_4793_);
if (v_isSharedCheck_4842_ == 0)
{
lean_object* v_unused_4843_; lean_object* v_unused_4844_; lean_object* v_unused_4845_; lean_object* v_unused_4846_; lean_object* v_unused_4847_; 
v_unused_4843_ = lean_ctor_get(v_r_4793_, 4);
lean_dec(v_unused_4843_);
v_unused_4844_ = lean_ctor_get(v_r_4793_, 3);
lean_dec(v_unused_4844_);
v_unused_4845_ = lean_ctor_get(v_r_4793_, 2);
lean_dec(v_unused_4845_);
v_unused_4846_ = lean_ctor_get(v_r_4793_, 1);
lean_dec(v_unused_4846_);
v_unused_4847_ = lean_ctor_get(v_r_4793_, 0);
lean_dec(v_unused_4847_);
v___x_4815_ = v_r_4793_;
v_isShared_4816_ = v_isSharedCheck_4842_;
goto v_resetjp_4814_;
}
else
{
lean_dec(v_r_4793_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4842_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___y_4820_; lean_object* v___y_4821_; lean_object* v___y_4822_; lean_object* v___x_4830_; lean_object* v___y_4832_; 
v___x_4817_ = lean_nat_add(v___x_4787_, v_size_4789_);
lean_dec(v_size_4789_);
v___x_4818_ = lean_nat_add(v___x_4817_, v_size_4788_);
lean_dec(v___x_4817_);
v___x_4830_ = lean_nat_add(v___x_4787_, v_size_4805_);
if (lean_obj_tag(v_l_4809_) == 0)
{
lean_object* v_size_4840_; 
v_size_4840_ = lean_ctor_get(v_l_4809_, 0);
lean_inc(v_size_4840_);
v___y_4832_ = v_size_4840_;
goto v___jp_4831_;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___y_4832_ = v___x_4841_;
goto v___jp_4831_;
}
v___jp_4819_:
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4823_ = lean_nat_add(v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec(v___y_4821_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 4, v_r_4642_);
lean_ctor_set(v___x_4815_, 3, v_r_4810_);
lean_ctor_set(v___x_4815_, 2, v_v_4640_);
lean_ctor_set(v___x_4815_, 1, v_k_4639_);
lean_ctor_set(v___x_4815_, 0, v___x_4823_);
v___x_4825_ = v___x_4815_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4823_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4829_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4829_, 3, v_r_4810_);
lean_ctor_set(v_reuseFailAlloc_4829_, 4, v_r_4642_);
v___x_4825_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
lean_object* v___x_4827_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 4, v___x_4825_);
lean_ctor_set(v___x_4803_, 3, v___y_4820_);
lean_ctor_set(v___x_4803_, 2, v_v_4808_);
lean_ctor_set(v___x_4803_, 1, v_k_4807_);
lean_ctor_set(v___x_4803_, 0, v___x_4818_);
v___x_4827_ = v___x_4803_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_k_4807_);
lean_ctor_set(v_reuseFailAlloc_4828_, 2, v_v_4808_);
lean_ctor_set(v_reuseFailAlloc_4828_, 3, v___y_4820_);
lean_ctor_set(v_reuseFailAlloc_4828_, 4, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
v___jp_4831_:
{
lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4833_ = lean_nat_add(v___x_4830_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec(v___x_4830_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_l_4809_);
lean_ctor_set(v___x_4644_, 3, v_l_4792_);
lean_ctor_set(v___x_4644_, 2, v_v_4791_);
lean_ctor_set(v___x_4644_, 1, v_k_4790_);
lean_ctor_set(v___x_4644_, 0, v___x_4833_);
v___x_4835_ = v___x_4644_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4833_);
lean_ctor_set(v_reuseFailAlloc_4839_, 1, v_k_4790_);
lean_ctor_set(v_reuseFailAlloc_4839_, 2, v_v_4791_);
lean_ctor_set(v_reuseFailAlloc_4839_, 3, v_l_4792_);
lean_ctor_set(v_reuseFailAlloc_4839_, 4, v_l_4809_);
v___x_4835_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_nat_add(v___x_4787_, v_size_4788_);
if (lean_obj_tag(v_r_4810_) == 0)
{
lean_object* v_size_4837_; 
v_size_4837_ = lean_ctor_get(v_r_4810_, 0);
lean_inc(v_size_4837_);
v___y_4820_ = v___x_4835_;
v___y_4821_ = v___x_4836_;
v___y_4822_ = v_size_4837_;
goto v___jp_4819_;
}
else
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_unsigned_to_nat(0u);
v___y_4820_ = v___x_4835_;
v___y_4821_ = v___x_4836_;
v___y_4822_ = v___x_4838_;
goto v___jp_4819_;
}
}
}
}
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
lean_del_object(v___x_4644_);
v___x_4848_ = lean_nat_add(v___x_4787_, v_size_4789_);
lean_dec(v_size_4789_);
v___x_4849_ = lean_nat_add(v___x_4848_, v_size_4788_);
lean_dec(v___x_4848_);
v___x_4850_ = lean_nat_add(v___x_4787_, v_size_4788_);
v___x_4851_ = lean_nat_add(v___x_4850_, v_size_4806_);
lean_dec(v___x_4850_);
lean_inc_ref(v_r_4642_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 4, v_r_4642_);
lean_ctor_set(v___x_4803_, 3, v_r_4793_);
lean_ctor_set(v___x_4803_, 2, v_v_4640_);
lean_ctor_set(v___x_4803_, 1, v_k_4639_);
lean_ctor_set(v___x_4803_, 0, v___x_4851_);
v___x_4853_ = v___x_4803_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4866_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4866_, 3, v_r_4793_);
lean_ctor_set(v_reuseFailAlloc_4866_, 4, v_r_4642_);
v___x_4853_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
v_isSharedCheck_4860_ = !lean_is_exclusive(v_r_4642_);
if (v_isSharedCheck_4860_ == 0)
{
lean_object* v_unused_4861_; lean_object* v_unused_4862_; lean_object* v_unused_4863_; lean_object* v_unused_4864_; lean_object* v_unused_4865_; 
v_unused_4861_ = lean_ctor_get(v_r_4642_, 4);
lean_dec(v_unused_4861_);
v_unused_4862_ = lean_ctor_get(v_r_4642_, 3);
lean_dec(v_unused_4862_);
v_unused_4863_ = lean_ctor_get(v_r_4642_, 2);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_r_4642_, 1);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_r_4642_, 0);
lean_dec(v_unused_4865_);
v___x_4855_ = v_r_4642_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_dec(v_r_4642_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 4, v___x_4853_);
lean_ctor_set(v___x_4855_, 3, v_l_4792_);
lean_ctor_set(v___x_4855_, 2, v_v_4791_);
lean_ctor_set(v___x_4855_, 1, v_k_4790_);
lean_ctor_set(v___x_4855_, 0, v___x_4849_);
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4859_, 1, v_k_4790_);
lean_ctor_set(v_reuseFailAlloc_4859_, 2, v_v_4791_);
lean_ctor_set(v_reuseFailAlloc_4859_, 3, v_l_4792_);
lean_ctor_set(v_reuseFailAlloc_4859_, 4, v___x_4853_);
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
}
}
else
{
lean_object* v_l_4873_; 
v_l_4873_ = lean_ctor_get(v_impl_4786_, 3);
lean_inc(v_l_4873_);
if (lean_obj_tag(v_l_4873_) == 0)
{
lean_object* v_r_4874_; lean_object* v_k_4875_; lean_object* v_v_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4887_; 
v_r_4874_ = lean_ctor_get(v_impl_4786_, 4);
v_k_4875_ = lean_ctor_get(v_impl_4786_, 1);
v_v_4876_ = lean_ctor_get(v_impl_4786_, 2);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_impl_4786_);
if (v_isSharedCheck_4887_ == 0)
{
lean_object* v_unused_4888_; lean_object* v_unused_4889_; 
v_unused_4888_ = lean_ctor_get(v_impl_4786_, 3);
lean_dec(v_unused_4888_);
v_unused_4889_ = lean_ctor_get(v_impl_4786_, 0);
lean_dec(v_unused_4889_);
v___x_4878_ = v_impl_4786_;
v_isShared_4879_ = v_isSharedCheck_4887_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_r_4874_);
lean_inc(v_v_4876_);
lean_inc(v_k_4875_);
lean_dec(v_impl_4786_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4887_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4874_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 3, v_r_4874_);
lean_ctor_set(v___x_4878_, 2, v_v_4640_);
lean_ctor_set(v___x_4878_, 1, v_k_4639_);
lean_ctor_set(v___x_4878_, 0, v___x_4787_);
v___x_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4886_, 3, v_r_4874_);
lean_ctor_set(v_reuseFailAlloc_4886_, 4, v_r_4874_);
v___x_4882_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4884_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v___x_4882_);
lean_ctor_set(v___x_4644_, 3, v_l_4873_);
lean_ctor_set(v___x_4644_, 2, v_v_4876_);
lean_ctor_set(v___x_4644_, 1, v_k_4875_);
lean_ctor_set(v___x_4644_, 0, v___x_4880_);
v___x_4884_ = v___x_4644_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_k_4875_);
lean_ctor_set(v_reuseFailAlloc_4885_, 2, v_v_4876_);
lean_ctor_set(v_reuseFailAlloc_4885_, 3, v_l_4873_);
lean_ctor_set(v_reuseFailAlloc_4885_, 4, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_object* v_r_4890_; 
v_r_4890_ = lean_ctor_get(v_impl_4786_, 4);
lean_inc(v_r_4890_);
if (lean_obj_tag(v_r_4890_) == 0)
{
lean_object* v_k_4891_; lean_object* v_v_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4915_; 
v_k_4891_ = lean_ctor_get(v_impl_4786_, 1);
v_v_4892_ = lean_ctor_get(v_impl_4786_, 2);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_impl_4786_);
if (v_isSharedCheck_4915_ == 0)
{
lean_object* v_unused_4916_; lean_object* v_unused_4917_; lean_object* v_unused_4918_; 
v_unused_4916_ = lean_ctor_get(v_impl_4786_, 4);
lean_dec(v_unused_4916_);
v_unused_4917_ = lean_ctor_get(v_impl_4786_, 3);
lean_dec(v_unused_4917_);
v_unused_4918_ = lean_ctor_get(v_impl_4786_, 0);
lean_dec(v_unused_4918_);
v___x_4894_ = v_impl_4786_;
v_isShared_4895_ = v_isSharedCheck_4915_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_v_4892_);
lean_inc(v_k_4891_);
lean_dec(v_impl_4786_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4915_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v_k_4896_; lean_object* v_v_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4911_; 
v_k_4896_ = lean_ctor_get(v_r_4890_, 1);
v_v_4897_ = lean_ctor_get(v_r_4890_, 2);
v_isSharedCheck_4911_ = !lean_is_exclusive(v_r_4890_);
if (v_isSharedCheck_4911_ == 0)
{
lean_object* v_unused_4912_; lean_object* v_unused_4913_; lean_object* v_unused_4914_; 
v_unused_4912_ = lean_ctor_get(v_r_4890_, 4);
lean_dec(v_unused_4912_);
v_unused_4913_ = lean_ctor_get(v_r_4890_, 3);
lean_dec(v_unused_4913_);
v_unused_4914_ = lean_ctor_get(v_r_4890_, 0);
lean_dec(v_unused_4914_);
v___x_4899_ = v_r_4890_;
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_v_4897_);
lean_inc(v_k_4896_);
lean_dec(v_r_4890_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4901_ = lean_unsigned_to_nat(3u);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 4, v_l_4873_);
lean_ctor_set(v___x_4899_, 3, v_l_4873_);
lean_ctor_set(v___x_4899_, 2, v_v_4892_);
lean_ctor_set(v___x_4899_, 1, v_k_4891_);
lean_ctor_set(v___x_4899_, 0, v___x_4787_);
v___x_4903_ = v___x_4899_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_k_4891_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_v_4892_);
lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_l_4873_);
lean_ctor_set(v_reuseFailAlloc_4910_, 4, v_l_4873_);
v___x_4903_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4905_; 
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 4, v_l_4873_);
lean_ctor_set(v___x_4894_, 2, v_v_4640_);
lean_ctor_set(v___x_4894_, 1, v_k_4639_);
lean_ctor_set(v___x_4894_, 0, v___x_4787_);
v___x_4905_ = v___x_4894_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4909_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4909_, 3, v_l_4873_);
lean_ctor_set(v_reuseFailAlloc_4909_, 4, v_l_4873_);
v___x_4905_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
lean_object* v___x_4907_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v___x_4905_);
lean_ctor_set(v___x_4644_, 3, v___x_4903_);
lean_ctor_set(v___x_4644_, 2, v_v_4897_);
lean_ctor_set(v___x_4644_, 1, v_k_4896_);
lean_ctor_set(v___x_4644_, 0, v___x_4901_);
v___x_4907_ = v___x_4644_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4901_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_k_4896_);
lean_ctor_set(v_reuseFailAlloc_4908_, 2, v_v_4897_);
lean_ctor_set(v_reuseFailAlloc_4908_, 3, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4908_, 4, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
}
}
else
{
lean_object* v___x_4919_; lean_object* v___x_4921_; 
v___x_4919_ = lean_unsigned_to_nat(2u);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_r_4890_);
lean_ctor_set(v___x_4644_, 3, v_impl_4786_);
lean_ctor_set(v___x_4644_, 0, v___x_4919_);
v___x_4921_ = v___x_4644_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_impl_4786_);
lean_ctor_set(v_reuseFailAlloc_4922_, 4, v_r_4890_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = lean_unsigned_to_nat(1u);
v___x_4925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
lean_ctor_set(v___x_4925_, 1, v_k_4635_);
lean_ctor_set(v___x_4925_, 2, v_v_4636_);
lean_ctor_set(v___x_4925_, 3, v_t_4637_);
lean_ctor_set(v___x_4925_, 4, v_t_4637_);
return v___x_4925_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_4926_, lean_object* v_t_4927_){
_start:
{
if (lean_obj_tag(v_t_4927_) == 0)
{
lean_object* v_k_4928_; lean_object* v_l_4929_; lean_object* v_r_4930_; uint8_t v___x_4931_; 
v_k_4928_ = lean_ctor_get(v_t_4927_, 1);
v_l_4929_ = lean_ctor_get(v_t_4927_, 3);
v_r_4930_ = lean_ctor_get(v_t_4927_, 4);
v___x_4931_ = lean_nat_dec_lt(v_k_4928_, v_k_4926_);
if (v___x_4931_ == 0)
{
uint8_t v___x_4932_; 
v___x_4932_ = lean_nat_dec_eq(v_k_4928_, v_k_4926_);
if (v___x_4932_ == 0)
{
v_t_4927_ = v_r_4930_;
goto _start;
}
else
{
return v___x_4932_;
}
}
else
{
v_t_4927_ = v_l_4929_;
goto _start;
}
}
else
{
uint8_t v___x_4935_; 
v___x_4935_ = 0;
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_4936_, lean_object* v_t_4937_){
_start:
{
uint8_t v_res_4938_; lean_object* v_r_4939_; 
v_res_4938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4936_, v_t_4937_);
lean_dec(v_t_4937_);
lean_dec(v_k_4936_);
v_r_4939_ = lean_box(v_res_4938_);
return v_r_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_4940_, lean_object* v_e_4941_){
_start:
{
lean_object* v_defaultInstances_4942_; lean_object* v_priorities_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4970_; 
v_defaultInstances_4942_ = lean_ctor_get(v_d_4940_, 0);
v_priorities_4943_ = lean_ctor_get(v_d_4940_, 1);
v_isSharedCheck_4970_ = !lean_is_exclusive(v_d_4940_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4945_ = v_d_4940_;
v_isShared_4946_ = v_isSharedCheck_4970_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_priorities_4943_);
lean_inc(v_defaultInstances_4942_);
lean_dec(v_d_4940_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4970_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v_className_4947_; lean_object* v_instanceName_4948_; lean_object* v_priority_4949_; lean_object* v___y_4951_; uint8_t v___x_4967_; 
v_className_4947_ = lean_ctor_get(v_e_4941_, 0);
lean_inc(v_className_4947_);
v_instanceName_4948_ = lean_ctor_get(v_e_4941_, 1);
lean_inc(v_instanceName_4948_);
v_priority_4949_ = lean_ctor_get(v_e_4941_, 2);
lean_inc(v_priority_4949_);
lean_dec_ref(v_e_4941_);
v___x_4967_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_4949_, v_priorities_4943_);
if (v___x_4967_ == 0)
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = lean_box(0);
lean_inc(v_priority_4949_);
v___x_4969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_4949_, v___x_4968_, v_priorities_4943_);
v___y_4951_ = v___x_4969_;
goto v___jp_4950_;
}
else
{
v___y_4951_ = v_priorities_4943_;
goto v___jp_4950_;
}
v___jp_4950_:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_4942_, v_className_4947_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4958_; 
v___x_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4953_, 0, v_instanceName_4948_);
lean_ctor_set(v___x_4953_, 1, v_priority_4949_);
v___x_4954_ = lean_box(0);
v___x_4955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4953_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4947_, v___x_4955_, v_defaultInstances_4942_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___y_4951_);
lean_ctor_set(v___x_4945_, 0, v___x_4956_);
v___x_4958_ = v___x_4945_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___y_4951_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
else
{
lean_object* v_val_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v_val_4960_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_val_4960_);
lean_dec_ref(v___x_4952_);
v___x_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4961_, 0, v_instanceName_4948_);
lean_ctor_set(v___x_4961_, 1, v_priority_4949_);
v___x_4962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4961_);
lean_ctor_set(v___x_4962_, 1, v_val_4960_);
v___x_4963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4947_, v___x_4962_, v_defaultInstances_4942_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___y_4951_);
lean_ctor_set(v___x_4945_, 0, v___x_4963_);
v___x_4965_ = v___x_4945_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
lean_ctor_set(v_reuseFailAlloc_4966_, 1, v___y_4951_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_4971_, lean_object* v_k_4972_, lean_object* v_t_4973_){
_start:
{
uint8_t v___x_4974_; 
v___x_4974_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4972_, v_t_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_4975_, lean_object* v_k_4976_, lean_object* v_t_4977_){
_start:
{
uint8_t v_res_4978_; lean_object* v_r_4979_; 
v_res_4978_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_4975_, v_k_4976_, v_t_4977_);
lean_dec(v_t_4977_);
lean_dec(v_k_4976_);
v_r_4979_ = lean_box(v_res_4978_);
return v_r_4979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_4980_, lean_object* v_k_4981_, lean_object* v_v_4982_, lean_object* v_t_4983_, lean_object* v_hl_4984_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4981_, v_v_4982_, v_t_4983_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_4986_){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_array_mk(v_es_4986_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4988_, size_t v_i_4989_, size_t v_stop_4990_, lean_object* v_b_4991_){
_start:
{
uint8_t v___x_4992_; 
v___x_4992_ = lean_usize_dec_eq(v_i_4989_, v_stop_4990_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; lean_object* v___x_4994_; size_t v___x_4995_; size_t v___x_4996_; 
v___x_4993_ = lean_array_uget_borrowed(v_as_4988_, v_i_4989_);
lean_inc(v___x_4993_);
v___x_4994_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_4991_, v___x_4993_);
v___x_4995_ = ((size_t)1ULL);
v___x_4996_ = lean_usize_add(v_i_4989_, v___x_4995_);
v_i_4989_ = v___x_4996_;
v_b_4991_ = v___x_4994_;
goto _start;
}
else
{
return v_b_4991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4998_, lean_object* v_i_4999_, lean_object* v_stop_5000_, lean_object* v_b_5001_){
_start:
{
size_t v_i_boxed_5002_; size_t v_stop_boxed_5003_; lean_object* v_res_5004_; 
v_i_boxed_5002_ = lean_unbox_usize(v_i_4999_);
lean_dec(v_i_4999_);
v_stop_boxed_5003_ = lean_unbox_usize(v_stop_5000_);
lean_dec(v_stop_5000_);
v_res_5004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_4998_, v_i_boxed_5002_, v_stop_boxed_5003_, v_b_5001_);
lean_dec_ref(v_as_4998_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_5005_, size_t v_i_5006_, size_t v_stop_5007_, lean_object* v_b_5008_){
_start:
{
lean_object* v___y_5010_; uint8_t v___x_5014_; 
v___x_5014_ = lean_usize_dec_eq(v_i_5006_, v_stop_5007_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; uint8_t v___x_5018_; 
v___x_5015_ = lean_array_uget_borrowed(v_as_5005_, v_i_5006_);
v___x_5016_ = lean_unsigned_to_nat(0u);
v___x_5017_ = lean_array_get_size(v___x_5015_);
v___x_5018_ = lean_nat_dec_lt(v___x_5016_, v___x_5017_);
if (v___x_5018_ == 0)
{
v___y_5010_ = v_b_5008_;
goto v___jp_5009_;
}
else
{
uint8_t v___x_5019_; 
v___x_5019_ = lean_nat_dec_le(v___x_5017_, v___x_5017_);
if (v___x_5019_ == 0)
{
if (v___x_5018_ == 0)
{
v___y_5010_ = v_b_5008_;
goto v___jp_5009_;
}
else
{
size_t v___x_5020_; size_t v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = ((size_t)0ULL);
v___x_5021_ = lean_usize_of_nat(v___x_5017_);
v___x_5022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5015_, v___x_5020_, v___x_5021_, v_b_5008_);
v___y_5010_ = v___x_5022_;
goto v___jp_5009_;
}
}
else
{
size_t v___x_5023_; size_t v___x_5024_; lean_object* v___x_5025_; 
v___x_5023_ = ((size_t)0ULL);
v___x_5024_ = lean_usize_of_nat(v___x_5017_);
v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5015_, v___x_5023_, v___x_5024_, v_b_5008_);
v___y_5010_ = v___x_5025_;
goto v___jp_5009_;
}
}
}
else
{
return v_b_5008_;
}
v___jp_5009_:
{
size_t v___x_5011_; size_t v___x_5012_; 
v___x_5011_ = ((size_t)1ULL);
v___x_5012_ = lean_usize_add(v_i_5006_, v___x_5011_);
v_i_5006_ = v___x_5012_;
v_b_5008_ = v___y_5010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5026_, lean_object* v_i_5027_, lean_object* v_stop_5028_, lean_object* v_b_5029_){
_start:
{
size_t v_i_boxed_5030_; size_t v_stop_boxed_5031_; lean_object* v_res_5032_; 
v_i_boxed_5030_ = lean_unbox_usize(v_i_5027_);
lean_dec(v_i_5027_);
v_stop_boxed_5031_ = lean_unbox_usize(v_stop_5028_);
lean_dec(v_stop_5028_);
v_res_5032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5026_, v_i_boxed_5030_, v_stop_boxed_5031_, v_b_5029_);
lean_dec_ref(v_as_5026_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5033_, lean_object* v_as_5034_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; uint8_t v___x_5037_; 
v___x_5035_ = lean_unsigned_to_nat(0u);
v___x_5036_ = lean_array_get_size(v_as_5034_);
v___x_5037_ = lean_nat_dec_lt(v___x_5035_, v___x_5036_);
if (v___x_5037_ == 0)
{
return v_initState_5033_;
}
else
{
uint8_t v___x_5038_; 
v___x_5038_ = lean_nat_dec_le(v___x_5036_, v___x_5036_);
if (v___x_5038_ == 0)
{
if (v___x_5037_ == 0)
{
return v_initState_5033_;
}
else
{
size_t v___x_5039_; size_t v___x_5040_; lean_object* v___x_5041_; 
v___x_5039_ = ((size_t)0ULL);
v___x_5040_ = lean_usize_of_nat(v___x_5036_);
v___x_5041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5034_, v___x_5039_, v___x_5040_, v_initState_5033_);
return v___x_5041_;
}
}
else
{
size_t v___x_5042_; size_t v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = ((size_t)0ULL);
v___x_5043_ = lean_usize_of_nat(v___x_5036_);
v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5034_, v___x_5042_, v___x_5043_, v_initState_5033_);
return v___x_5044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5045_, lean_object* v_as_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5045_, v_as_5046_);
lean_dec_ref(v_as_5046_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5048_){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5049_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5050_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5049_, v_es_5048_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5051_);
lean_dec_ref(v_es_5051_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5070_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5069_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___x_5077_; lean_object* v_nextMacroScope_5078_; lean_object* v_ngen_5079_; lean_object* v_auxDeclNGen_5080_; lean_object* v_traceState_5081_; lean_object* v_messages_5082_; lean_object* v_infoState_5083_; lean_object* v_snapshotTasks_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5110_; 
v___x_5077_ = lean_st_ref_take(v___y_5075_);
v_nextMacroScope_5078_ = lean_ctor_get(v___x_5077_, 1);
v_ngen_5079_ = lean_ctor_get(v___x_5077_, 2);
v_auxDeclNGen_5080_ = lean_ctor_get(v___x_5077_, 3);
v_traceState_5081_ = lean_ctor_get(v___x_5077_, 4);
v_messages_5082_ = lean_ctor_get(v___x_5077_, 6);
v_infoState_5083_ = lean_ctor_get(v___x_5077_, 7);
v_snapshotTasks_5084_ = lean_ctor_get(v___x_5077_, 8);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5110_ == 0)
{
lean_object* v_unused_5111_; lean_object* v_unused_5112_; 
v_unused_5111_ = lean_ctor_get(v___x_5077_, 5);
lean_dec(v_unused_5111_);
v_unused_5112_ = lean_ctor_get(v___x_5077_, 0);
lean_dec(v_unused_5112_);
v___x_5086_ = v___x_5077_;
v_isShared_5087_ = v_isSharedCheck_5110_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_snapshotTasks_5084_);
lean_inc(v_infoState_5083_);
lean_inc(v_messages_5082_);
lean_inc(v_traceState_5081_);
lean_inc(v_auxDeclNGen_5080_);
lean_inc(v_ngen_5079_);
lean_inc(v_nextMacroScope_5078_);
lean_dec(v___x_5077_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5110_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5088_; lean_object* v___x_5090_; 
v___x_5088_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 5, v___x_5088_);
lean_ctor_set(v___x_5086_, 0, v_env_5073_);
v___x_5090_ = v___x_5086_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_env_5073_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v_nextMacroScope_5078_);
lean_ctor_set(v_reuseFailAlloc_5109_, 2, v_ngen_5079_);
lean_ctor_set(v_reuseFailAlloc_5109_, 3, v_auxDeclNGen_5080_);
lean_ctor_set(v_reuseFailAlloc_5109_, 4, v_traceState_5081_);
lean_ctor_set(v_reuseFailAlloc_5109_, 5, v___x_5088_);
lean_ctor_set(v_reuseFailAlloc_5109_, 6, v_messages_5082_);
lean_ctor_set(v_reuseFailAlloc_5109_, 7, v_infoState_5083_);
lean_ctor_set(v_reuseFailAlloc_5109_, 8, v_snapshotTasks_5084_);
v___x_5090_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v_mctx_5093_; lean_object* v_zetaDeltaFVarIds_5094_; lean_object* v_postponed_5095_; lean_object* v_diag_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5107_; 
v___x_5091_ = lean_st_ref_set(v___y_5075_, v___x_5090_);
v___x_5092_ = lean_st_ref_take(v___y_5074_);
v_mctx_5093_ = lean_ctor_get(v___x_5092_, 0);
v_zetaDeltaFVarIds_5094_ = lean_ctor_get(v___x_5092_, 2);
v_postponed_5095_ = lean_ctor_get(v___x_5092_, 3);
v_diag_5096_ = lean_ctor_get(v___x_5092_, 4);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v___x_5092_, 1);
lean_dec(v_unused_5108_);
v___x_5098_ = v___x_5092_;
v_isShared_5099_ = v_isSharedCheck_5107_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_diag_5096_);
lean_inc(v_postponed_5095_);
lean_inc(v_zetaDeltaFVarIds_5094_);
lean_inc(v_mctx_5093_);
lean_dec(v___x_5092_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5107_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 1, v___x_5100_);
v___x_5102_ = v___x_5098_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_mctx_5093_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5106_, 2, v_zetaDeltaFVarIds_5094_);
lean_ctor_set(v_reuseFailAlloc_5106_, 3, v_postponed_5095_);
lean_ctor_set(v_reuseFailAlloc_5106_, 4, v_diag_5096_);
v___x_5102_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5103_ = lean_st_ref_set(v___y_5074_, v___x_5102_);
v___x_5104_ = lean_box(0);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec(v___y_5114_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5118_, v___y_5120_, v___y_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
return v_res_5131_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5133_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5134_ = l_Lean_stringToMessageData(v___x_5133_);
return v___x_5134_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5137_ = l_Lean_stringToMessageData(v___x_5136_);
return v___x_5137_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5140_ = l_Lean_stringToMessageData(v___x_5139_);
return v___x_5140_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5142_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5143_ = l_Lean_stringToMessageData(v___x_5142_);
return v___x_5143_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5145_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5146_ = l_Lean_stringToMessageData(v___x_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5147_, lean_object* v_prio_5148_, lean_object* v_x_5149_, lean_object* v_type_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v___x_5156_; 
v___x_5156_ = l_Lean_Expr_getAppFn(v_type_5150_);
if (lean_obj_tag(v___x_5156_) == 4)
{
lean_object* v_declName_5157_; lean_object* v___y_5159_; lean_object* v___y_5160_; lean_object* v___y_5161_; lean_object* v___y_5162_; lean_object* v___x_5172_; lean_object* v_env_5173_; uint8_t v___x_5174_; 
v_declName_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc_n(v_declName_5157_, 2);
lean_dec_ref(v___x_5156_);
v___x_5172_ = lean_st_ref_get(v___y_5154_);
v_env_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc_ref(v_env_5173_);
lean_dec(v___x_5172_);
v___x_5174_ = lean_is_class(v_env_5173_, v_declName_5157_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
lean_dec(v_prio_5148_);
v___x_5175_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5176_ = l_Lean_MessageData_ofConstName(v_declName_5147_, v___x_5174_);
v___x_5177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5175_);
lean_ctor_set(v___x_5177_, 1, v___x_5176_);
v___x_5178_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5177_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
lean_inc(v_declName_5157_);
v___x_5180_ = l_Lean_MessageData_ofName(v_declName_5157_);
v___x_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5179_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5181_);
lean_ctor_set(v___x_5183_, 1, v___x_5182_);
v___x_5184_ = l_Lean_MessageData_ofConstName(v_declName_5157_, v___x_5174_);
v___x_5185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5183_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
v___x_5186_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5185_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5187_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
return v___x_5188_;
}
else
{
v___y_5159_ = v___y_5151_;
v___y_5160_ = v___y_5152_;
v___y_5161_ = v___y_5153_;
v___y_5162_ = v___y_5154_;
goto v___jp_5158_;
}
v___jp_5158_:
{
lean_object* v___x_5163_; lean_object* v_env_5164_; lean_object* v___x_5165_; lean_object* v_toEnvExtension_5166_; lean_object* v_asyncMode_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5163_ = lean_st_ref_get(v___y_5162_);
v_env_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc_ref(v_env_5164_);
lean_dec(v___x_5163_);
v___x_5165_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5166_ = lean_ctor_get(v___x_5165_, 0);
v_asyncMode_5167_ = lean_ctor_get(v_toEnvExtension_5166_, 2);
v___x_5168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5168_, 0, v_declName_5157_);
lean_ctor_set(v___x_5168_, 1, v_declName_5147_);
lean_ctor_set(v___x_5168_, 2, v_prio_5148_);
v___x_5169_ = lean_box(0);
v___x_5170_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5165_, v_env_5164_, v___x_5168_, v_asyncMode_5167_, v___x_5169_);
v___x_5171_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5170_, v___y_5160_, v___y_5162_);
return v___x_5171_;
}
}
else
{
lean_object* v___x_5189_; uint8_t v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
lean_dec_ref(v___x_5156_);
lean_dec(v_prio_5148_);
v___x_5189_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5190_ = 0;
v___x_5191_ = l_Lean_MessageData_ofConstName(v_declName_5147_, v___x_5190_);
v___x_5192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5189_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5192_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
v___x_5195_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5194_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
return v___x_5195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5196_, lean_object* v_prio_5197_, lean_object* v_x_5198_, lean_object* v_type_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5196_, v_prio_5197_, v_x_5198_, v_type_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec_ref(v_type_5199_);
lean_dec_ref(v_x_5198_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5206_, lean_object* v_prio_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v___x_5213_; lean_object* v_env_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; 
v___x_5213_ = lean_st_ref_get(v_a_5211_);
v_env_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc_ref(v_env_5214_);
lean_dec(v___x_5213_);
v___x_5215_ = 0;
lean_inc(v_declName_5206_);
v___x_5216_ = l_Lean_Environment_find_x3f(v_env_5214_, v_declName_5206_, v___x_5215_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec(v_prio_5207_);
v___x_5217_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5218_ = l_Lean_MessageData_ofConstName(v_declName_5206_, v___x_5215_);
v___x_5219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5217_);
lean_ctor_set(v___x_5219_, 1, v___x_5218_);
v___x_5220_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5219_);
lean_ctor_set(v___x_5221_, 1, v___x_5220_);
v___x_5222_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5221_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
return v___x_5222_;
}
else
{
lean_object* v_val_5223_; lean_object* v___f_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v_val_5223_ = lean_ctor_get(v___x_5216_, 0);
lean_inc(v_val_5223_);
lean_dec_ref(v___x_5216_);
v___f_5224_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5224_, 0, v_declName_5206_);
lean_closure_set(v___f_5224_, 1, v_prio_5207_);
v___x_5225_ = l_Lean_ConstantInfo_type(v_val_5223_);
lean_dec(v_val_5223_);
v___x_5226_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5225_, v___f_5224_, v___x_5215_, v___x_5215_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
return v___x_5226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5227_, lean_object* v_prio_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Lean_Meta_addDefaultInstance(v_declName_5227_, v_prio_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
return v_res_5234_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5236_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5237_ = l_Lean_stringToMessageData(v___x_5236_);
return v___x_5237_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5239_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5240_ = l_Lean_stringToMessageData(v___x_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5244_, uint8_t v_kind_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___y_5255_; 
v___x_5249_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5250_ = l_Lean_MessageData_ofName(v_name_5244_);
v___x_5251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5249_);
lean_ctor_set(v___x_5251_, 1, v___x_5250_);
v___x_5252_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5251_);
lean_ctor_set(v___x_5253_, 1, v___x_5252_);
switch(v_kind_5245_)
{
case 0:
{
lean_object* v___x_5262_; 
v___x_5262_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5255_ = v___x_5262_;
goto v___jp_5254_;
}
case 1:
{
lean_object* v___x_5263_; 
v___x_5263_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5255_ = v___x_5263_;
goto v___jp_5254_;
}
default: 
{
lean_object* v___x_5264_; 
v___x_5264_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5255_ = v___x_5264_;
goto v___jp_5254_;
}
}
v___jp_5254_:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
lean_inc_ref(v___y_5255_);
v___x_5256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5256_, 0, v___y_5255_);
v___x_5257_ = l_Lean_MessageData_ofFormat(v___x_5256_);
v___x_5258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5253_);
lean_ctor_set(v___x_5258_, 1, v___x_5257_);
v___x_5259_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5258_);
lean_ctor_set(v___x_5260_, 1, v___x_5259_);
v___x_5261_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5260_, v___y_5246_, v___y_5247_);
return v___x_5261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5265_, lean_object* v_kind_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
uint8_t v_kind_boxed_5270_; lean_object* v_res_5271_; 
v_kind_boxed_5270_ = lean_unbox(v_kind_5266_);
v_res_5271_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5265_, v_kind_boxed_5270_, v___y_5267_, v___y_5268_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5272_, lean_object* v___x_5273_, lean_object* v___x_5274_, lean_object* v_declName_5275_, lean_object* v_stx_5276_, uint8_t v_kind_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5281_ = lean_unsigned_to_nat(1u);
v___x_5282_ = l_Lean_Syntax_getArg(v_stx_5276_, v___x_5281_);
v___x_5283_ = l_Lean_getAttrParamOptPrio(v___x_5282_, v___y_5278_, v___y_5279_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v___y_5286_; lean_object* v___y_5287_; uint8_t v___x_5318_; uint8_t v___x_5319_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
lean_inc(v_a_5284_);
lean_dec_ref(v___x_5283_);
v___x_5318_ = 0;
v___x_5319_ = l_Lean_instBEqAttributeKind_beq(v_kind_5277_, v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
lean_dec(v_a_5284_);
lean_dec(v_declName_5275_);
lean_dec(v___x_5273_);
lean_dec(v___x_5272_);
v___x_5320_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5274_, v_kind_5277_, v___y_5278_, v___y_5279_);
return v___x_5320_;
}
else
{
lean_dec(v___x_5274_);
v___y_5286_ = v___y_5278_;
v___y_5287_ = v___y_5279_;
goto v___jp_5285_;
}
v___jp_5285_:
{
uint8_t v___x_5288_; uint8_t v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; size_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5288_ = 0;
v___x_5289_ = 1;
v___x_5290_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5291_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5292_ = lean_unsigned_to_nat(32u);
v___x_5293_ = lean_mk_empty_array_with_capacity(v___x_5292_);
v___x_5294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5295_ = ((size_t)5ULL);
lean_inc_n(v___x_5272_, 6);
v___x_5296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5296_, 0, v___x_5294_);
lean_ctor_set(v___x_5296_, 1, v___x_5293_);
lean_ctor_set(v___x_5296_, 2, v___x_5272_);
lean_ctor_set(v___x_5296_, 3, v___x_5272_);
lean_ctor_set_usize(v___x_5296_, 4, v___x_5295_);
v___x_5297_ = lean_box(1);
lean_inc_ref(v___x_5296_);
v___x_5298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5291_);
lean_ctor_set(v___x_5298_, 1, v___x_5296_);
lean_ctor_set(v___x_5298_, 2, v___x_5297_);
v___x_5299_ = lean_mk_empty_array_with_capacity(v___x_5272_);
v___x_5300_ = lean_box(0);
lean_inc(v___x_5273_);
v___x_5301_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5301_, 0, v___x_5290_);
lean_ctor_set(v___x_5301_, 1, v___x_5273_);
lean_ctor_set(v___x_5301_, 2, v___x_5298_);
lean_ctor_set(v___x_5301_, 3, v___x_5299_);
lean_ctor_set(v___x_5301_, 4, v___x_5300_);
lean_ctor_set(v___x_5301_, 5, v___x_5272_);
lean_ctor_set(v___x_5301_, 6, v___x_5300_);
lean_ctor_set_uint8(v___x_5301_, sizeof(void*)*7, v___x_5288_);
lean_ctor_set_uint8(v___x_5301_, sizeof(void*)*7 + 1, v___x_5288_);
lean_ctor_set_uint8(v___x_5301_, sizeof(void*)*7 + 2, v___x_5288_);
lean_ctor_set_uint8(v___x_5301_, sizeof(void*)*7 + 3, v___x_5289_);
v___x_5302_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5272_);
lean_ctor_set(v___x_5302_, 1, v___x_5272_);
lean_ctor_set(v___x_5302_, 2, v___x_5272_);
lean_ctor_set(v___x_5302_, 3, v___x_5272_);
lean_ctor_set(v___x_5302_, 4, v___x_5291_);
lean_ctor_set(v___x_5302_, 5, v___x_5291_);
lean_ctor_set(v___x_5302_, 6, v___x_5291_);
lean_ctor_set(v___x_5302_, 7, v___x_5291_);
lean_ctor_set(v___x_5302_, 8, v___x_5291_);
lean_ctor_set(v___x_5302_, 9, v___x_5291_);
v___x_5303_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5304_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5302_);
lean_ctor_set(v___x_5305_, 1, v___x_5303_);
lean_ctor_set(v___x_5305_, 2, v___x_5273_);
lean_ctor_set(v___x_5305_, 3, v___x_5296_);
lean_ctor_set(v___x_5305_, 4, v___x_5304_);
v___x_5306_ = lean_st_mk_ref(v___x_5305_);
v___x_5307_ = l_Lean_Meta_addDefaultInstance(v_declName_5275_, v_a_5284_, v___x_5301_, v___x_5306_, v___y_5286_, v___y_5287_);
lean_dec_ref(v___x_5301_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5316_; 
v_isSharedCheck_5316_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5316_ == 0)
{
lean_object* v_unused_5317_; 
v_unused_5317_ = lean_ctor_get(v___x_5307_, 0);
lean_dec(v_unused_5317_);
v___x_5309_ = v___x_5307_;
v_isShared_5310_ = v_isSharedCheck_5316_;
goto v_resetjp_5308_;
}
else
{
lean_dec(v___x_5307_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5316_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5314_; 
v___x_5311_ = lean_st_ref_get(v___x_5306_);
lean_dec(v___x_5306_);
lean_dec(v___x_5311_);
v___x_5312_ = lean_box(0);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5312_);
v___x_5314_ = v___x_5309_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5312_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
}
else
{
lean_dec(v___x_5306_);
return v___x_5307_;
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec(v_declName_5275_);
lean_dec(v___x_5274_);
lean_dec(v___x_5273_);
lean_dec(v___x_5272_);
v_a_5321_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5283_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5283_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5329_, lean_object* v___x_5330_, lean_object* v___x_5331_, lean_object* v_declName_5332_, lean_object* v_stx_5333_, lean_object* v_kind_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
uint8_t v_kind_boxed_5338_; lean_object* v_res_5339_; 
v_kind_boxed_5338_ = lean_unbox(v_kind_5334_);
v_res_5339_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5329_, v___x_5330_, v___x_5331_, v_declName_5332_, v_stx_5333_, v_kind_boxed_5338_, v___y_5335_, v___y_5336_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v_stx_5333_);
return v_res_5339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5341_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5342_ = l_Lean_stringToMessageData(v___x_5341_);
return v___x_5342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5345_ = l_Lean_stringToMessageData(v___x_5344_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5346_, lean_object* v_decl_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5351_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5352_ = l_Lean_MessageData_ofName(v___x_5346_);
v___x_5353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5351_);
lean_ctor_set(v___x_5353_, 1, v___x_5352_);
v___x_5354_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5353_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
v___x_5356_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5355_, v___y_5348_, v___y_5349_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5357_, lean_object* v_decl_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5357_, v_decl_5358_, v___y_5359_, v___y_5360_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec(v_decl_5358_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5396_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5397_ = l_Lean_registerBuiltinAttribute(v___x_5396_);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v___x_5398_; uint8_t v___x_5399_; lean_object* v___x_5400_; 
lean_dec_ref(v___x_5397_);
v___x_5398_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5399_ = 0;
v___x_5400_ = l_Lean_registerTraceClass(v___x_5398_, v___x_5399_, v___x_5395_);
return v___x_5400_;
}
else
{
return v___x_5397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5403_, lean_object* v_name_5404_, uint8_t v_kind_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5404_, v_kind_5405_, v___y_5406_, v___y_5407_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5410_, lean_object* v_name_5411_, lean_object* v_kind_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
uint8_t v_kind_boxed_5416_; lean_object* v_res_5417_; 
v_kind_boxed_5416_ = lean_unbox(v_kind_5412_);
v_res_5417_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5410_, v_name_5411_, v_kind_boxed_5416_, v___y_5413_, v___y_5414_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5418_, lean_object* v_toPure_5419_, lean_object* v_____do__lift_5420_){
_start:
{
lean_object* v___x_5421_; lean_object* v_toEnvExtension_5422_; lean_object* v_asyncMode_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v_priorities_5426_; lean_object* v___x_5427_; 
v___x_5421_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5422_ = lean_ctor_get(v___x_5421_, 0);
v_asyncMode_5423_ = lean_ctor_get(v_toEnvExtension_5422_, 2);
v___x_5424_ = lean_box(0);
v___x_5425_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5418_, v___x_5421_, v_____do__lift_5420_, v_asyncMode_5423_, v___x_5424_);
v_priorities_5426_ = lean_ctor_get(v___x_5425_, 1);
lean_inc(v_priorities_5426_);
lean_dec(v___x_5425_);
v___x_5427_ = lean_apply_2(v_toPure_5419_, lean_box(0), v_priorities_5426_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5428_, lean_object* v_inst_5429_){
_start:
{
lean_object* v_toApplicative_5430_; lean_object* v_toBind_5431_; lean_object* v_getEnv_5432_; lean_object* v_toPure_5433_; lean_object* v___x_5434_; lean_object* v___f_5435_; lean_object* v___x_5436_; 
v_toApplicative_5430_ = lean_ctor_get(v_inst_5428_, 0);
lean_inc_ref(v_toApplicative_5430_);
v_toBind_5431_ = lean_ctor_get(v_inst_5428_, 1);
lean_inc(v_toBind_5431_);
lean_dec_ref(v_inst_5428_);
v_getEnv_5432_ = lean_ctor_get(v_inst_5429_, 0);
lean_inc(v_getEnv_5432_);
lean_dec_ref(v_inst_5429_);
v_toPure_5433_ = lean_ctor_get(v_toApplicative_5430_, 1);
lean_inc(v_toPure_5433_);
lean_dec_ref(v_toApplicative_5430_);
v___x_5434_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5435_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5435_, 0, v___x_5434_);
lean_closure_set(v___f_5435_, 1, v_toPure_5433_);
v___x_5436_ = lean_apply_4(v_toBind_5431_, lean_box(0), lean_box(0), v_getEnv_5432_, v___f_5435_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5437_, lean_object* v_inst_5438_, lean_object* v_inst_5439_){
_start:
{
lean_object* v___x_5440_; 
v___x_5440_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5438_, v_inst_5439_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5441_, lean_object* v_className_5442_, lean_object* v_toPure_5443_, lean_object* v_____do__lift_5444_){
_start:
{
lean_object* v___x_5445_; lean_object* v_toEnvExtension_5446_; lean_object* v_asyncMode_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v_defaultInstances_5450_; lean_object* v___x_5451_; 
v___x_5445_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5446_ = lean_ctor_get(v___x_5445_, 0);
v_asyncMode_5447_ = lean_ctor_get(v_toEnvExtension_5446_, 2);
v___x_5448_ = lean_box(0);
v___x_5449_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5441_, v___x_5445_, v_____do__lift_5444_, v_asyncMode_5447_, v___x_5448_);
v_defaultInstances_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_defaultInstances_5450_);
lean_dec(v___x_5449_);
v___x_5451_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5450_, v_className_5442_);
lean_dec(v_defaultInstances_5450_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5452_ = lean_box(0);
v___x_5453_ = lean_apply_2(v_toPure_5443_, lean_box(0), v___x_5452_);
return v___x_5453_;
}
else
{
lean_object* v_val_5454_; lean_object* v___x_5455_; 
v_val_5454_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_val_5454_);
lean_dec_ref(v___x_5451_);
v___x_5455_ = lean_apply_2(v_toPure_5443_, lean_box(0), v_val_5454_);
return v___x_5455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5456_, lean_object* v_className_5457_, lean_object* v_toPure_5458_, lean_object* v_____do__lift_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5456_, v_className_5457_, v_toPure_5458_, v_____do__lift_5459_);
lean_dec(v_className_5457_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5461_, lean_object* v_inst_5462_, lean_object* v_className_5463_){
_start:
{
lean_object* v_toApplicative_5464_; lean_object* v_toBind_5465_; lean_object* v_getEnv_5466_; lean_object* v_toPure_5467_; lean_object* v___x_5468_; lean_object* v___f_5469_; lean_object* v___x_5470_; 
v_toApplicative_5464_ = lean_ctor_get(v_inst_5461_, 0);
lean_inc_ref(v_toApplicative_5464_);
v_toBind_5465_ = lean_ctor_get(v_inst_5461_, 1);
lean_inc(v_toBind_5465_);
lean_dec_ref(v_inst_5461_);
v_getEnv_5466_ = lean_ctor_get(v_inst_5462_, 0);
lean_inc(v_getEnv_5466_);
lean_dec_ref(v_inst_5462_);
v_toPure_5467_ = lean_ctor_get(v_toApplicative_5464_, 1);
lean_inc(v_toPure_5467_);
lean_dec_ref(v_toApplicative_5464_);
v___x_5468_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5469_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5469_, 0, v___x_5468_);
lean_closure_set(v___f_5469_, 1, v_className_5463_);
lean_closure_set(v___f_5469_, 2, v_toPure_5467_);
v___x_5470_ = lean_apply_4(v_toBind_5465_, lean_box(0), lean_box(0), v_getEnv_5466_, v___f_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5471_, lean_object* v_inst_5472_, lean_object* v_inst_5473_, lean_object* v_className_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5472_, v_inst_5473_, v_className_5474_);
return v___x_5475_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
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
