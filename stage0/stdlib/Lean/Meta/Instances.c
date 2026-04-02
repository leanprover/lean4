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
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value)}};
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
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
return v_res_62_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = ((lean_object*)(l_Lean_Meta_instInhabitedInstanceEntry_default___closed__2));
v___x_70_ = l_Lean_Expr_const___override(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4(void){
_start:
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_71_ = 0;
v___x_72_ = lean_box(0);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3, &l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3_once, _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3);
v___x_75_ = ((lean_object*)(l_Lean_Meta_instInhabitedInstanceEntry_default___closed__0));
v___x_76_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
lean_ctor_set(v___x_76_, 3, v___x_72_);
lean_ctor_set(v___x_76_, 4, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*5, v___x_71_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4, &l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_instInhabitedInstanceEntry_default;
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqInstanceEntry___lam__0(lean_object* v_e_u2081_79_, lean_object* v_e_u2082_80_){
_start:
{
lean_object* v_val_81_; lean_object* v_val_82_; uint8_t v___x_83_; 
v_val_81_ = lean_ctor_get(v_e_u2081_79_, 1);
v_val_82_ = lean_ctor_get(v_e_u2082_80_, 1);
v___x_83_ = lean_expr_eqv(v_val_81_, v_val_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqInstanceEntry___lam__0___boxed(lean_object* v_e_u2081_84_, lean_object* v_e_u2082_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_Meta_instBEqInstanceEntry___lam__0(v_e_u2081_84_, v_e_u2082_85_);
lean_dec_ref(v_e_u2082_85_);
lean_dec_ref(v_e_u2081_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatInstanceEntry___lam__0(lean_object* v_e_93_){
_start:
{
lean_object* v_globalName_x3f_94_; 
v_globalName_x3f_94_ = lean_ctor_get(v_e_93_, 3);
lean_inc(v_globalName_x3f_94_);
lean_dec_ref(v_e_93_);
if (lean_obj_tag(v_globalName_x3f_94_) == 1)
{
lean_object* v_val_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_104_; 
v_val_95_ = lean_ctor_get(v_globalName_x3f_94_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_globalName_x3f_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_97_ = v_globalName_x3f_94_;
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_val_95_);
lean_dec(v_globalName_x3f_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = 1;
v___x_100_ = l_Lean_Name_toString(v_val_95_, v___x_99_);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 3);
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_globalName_x3f_94_);
v___x_105_ = ((lean_object*)(l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__1));
return v___x_105_;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_108_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_object* v_00_u03b2_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__0(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__1(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__0, &l_Lean_Meta_instInhabitedInstances_default___closed__0_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__0);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__2(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_box(0));
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_118_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__1, &l_Lean_Meta_instInhabitedInstances_default___closed__1_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__1);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set(v___x_119_, 2, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__3, &l_Lean_Meta_instInhabitedInstances_default___closed__3_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__3);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_instInhabitedInstances_default;
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_ks_126_; lean_object* v_vs_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_151_; 
v_ks_126_ = lean_ctor_get(v_x_122_, 0);
v_vs_127_ = lean_ctor_get(v_x_122_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_151_ == 0)
{
v___x_129_ = v_x_122_;
v_isShared_130_ = v_isSharedCheck_151_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_vs_127_);
lean_inc(v_ks_126_);
lean_dec(v_x_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_151_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_array_get_size(v_ks_126_);
v___x_132_ = lean_nat_dec_lt(v_x_123_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_x_123_);
v___x_133_ = lean_array_push(v_ks_126_, v_x_124_);
v___x_134_ = lean_array_push(v_vs_127_, v_x_125_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_134_);
lean_ctor_set(v___x_129_, 0, v___x_133_);
v___x_136_ = v___x_129_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v_k_x27_138_; uint8_t v___x_139_; 
v_k_x27_138_ = lean_array_fget_borrowed(v_ks_126_, v_x_123_);
v___x_139_ = lean_name_eq(v_x_124_, v_k_x27_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
if (v_isShared_130_ == 0)
{
v___x_141_ = v___x_129_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_ks_126_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_vs_127_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v_x_123_, v___x_142_);
lean_dec(v_x_123_);
v_x_122_ = v___x_141_;
v_x_123_ = v___x_143_;
goto _start;
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_array_fset(v_ks_126_, v_x_123_, v_x_124_);
v___x_147_ = lean_array_fset(v_vs_127_, v_x_123_, v_x_125_);
lean_dec(v_x_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_147_);
lean_ctor_set(v___x_129_, 0, v___x_146_);
v___x_149_ = v___x_129_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(lean_object* v_n_152_, lean_object* v_k_153_, lean_object* v_v_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_n_152_, v___x_155_, v_k_153_, v_v_154_);
return v___x_156_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_157_; uint64_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1723u);
v___x_158_ = lean_uint64_of_nat(v___x_157_);
return v___x_158_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; 
v___x_159_ = ((size_t)5ULL);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_shift_left(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; 
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__0);
v___x_164_ = lean_usize_sub(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(lean_object* v_x_166_, size_t v_x_167_, size_t v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_es_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v_j_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_es_171_ = lean_ctor_get(v_x_166_, 0);
v___x_172_ = ((size_t)5ULL);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_175_ = lean_usize_land(v_x_167_, v___x_174_);
v_j_176_ = lean_usize_to_nat(v___x_175_);
v___x_177_ = lean_array_get_size(v_es_171_);
v___x_178_ = lean_nat_dec_lt(v_j_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_j_176_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
return v_x_166_;
}
else
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_215_; 
lean_inc_ref(v_es_171_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_x_166_, 0);
lean_dec(v_unused_216_);
v___x_180_ = v_x_166_;
v_isShared_181_ = v_isSharedCheck_215_;
goto v_resetjp_179_;
}
else
{
lean_dec(v_x_166_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_215_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_v_182_; lean_object* v___x_183_; lean_object* v_xs_x27_184_; lean_object* v___y_186_; 
v_v_182_ = lean_array_fget(v_es_171_, v_j_176_);
v___x_183_ = lean_box(0);
v_xs_x27_184_ = lean_array_fset(v_es_171_, v_j_176_, v___x_183_);
switch(lean_obj_tag(v_v_182_))
{
case 0:
{
lean_object* v_key_191_; lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_202_; 
v_key_191_ = lean_ctor_get(v_v_182_, 0);
v_val_192_ = lean_ctor_get(v_v_182_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_v_182_);
if (v_isSharedCheck_202_ == 0)
{
v___x_194_ = v_v_182_;
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_inc(v_key_191_);
lean_dec(v_v_182_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
uint8_t v___x_196_; 
v___x_196_ = lean_name_eq(v_x_169_, v_key_191_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_del_object(v___x_194_);
v___x_197_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_191_, v_val_192_, v_x_169_, v_x_170_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___y_186_ = v___x_198_;
goto v___jp_185_;
}
else
{
lean_object* v___x_200_; 
lean_dec(v_val_192_);
lean_dec(v_key_191_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v_x_170_);
lean_ctor_set(v___x_194_, 0, v_x_169_);
v___x_200_ = v___x_194_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_x_169_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_x_170_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v___y_186_ = v___x_200_;
goto v___jp_185_;
}
}
}
}
case 1:
{
lean_object* v_node_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_213_; 
v_node_203_ = lean_ctor_get(v_v_182_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_v_182_);
if (v_isSharedCheck_213_ == 0)
{
v___x_205_ = v_v_182_;
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_node_203_);
lean_dec(v_v_182_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_207_ = lean_usize_shift_right(v_x_167_, v___x_172_);
v___x_208_ = lean_usize_add(v_x_168_, v___x_173_);
v___x_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_node_203_, v___x_207_, v___x_208_, v_x_169_, v_x_170_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_209_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v___y_186_ = v___x_211_;
goto v___jp_185_;
}
}
}
default: 
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_x_169_);
lean_ctor_set(v___x_214_, 1, v_x_170_);
v___y_186_ = v___x_214_;
goto v___jp_185_;
}
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_array_fset(v_xs_x27_184_, v_j_176_, v___y_186_);
lean_dec(v_j_176_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_187_);
v___x_189_ = v___x_180_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
else
{
lean_object* v_ks_217_; lean_object* v_vs_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_238_; 
v_ks_217_ = lean_ctor_get(v_x_166_, 0);
v_vs_218_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_238_ == 0)
{
v___x_220_ = v_x_166_;
v_isShared_221_ = v_isSharedCheck_238_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_vs_218_);
lean_inc(v_ks_217_);
lean_dec(v_x_166_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_238_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_ks_217_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_vs_218_);
v___x_223_ = v_reuseFailAlloc_237_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v_newNode_224_; uint8_t v___y_226_; size_t v___x_232_; uint8_t v___x_233_; 
v_newNode_224_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v___x_223_, v_x_169_, v_x_170_);
v___x_232_ = ((size_t)7ULL);
v___x_233_ = lean_usize_dec_le(v___x_232_, v_x_168_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_224_);
v___x_235_ = lean_unsigned_to_nat(4u);
v___x_236_ = lean_nat_dec_lt(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
v___y_226_ = v___x_236_;
goto v___jp_225_;
}
else
{
v___y_226_ = v___x_233_;
goto v___jp_225_;
}
v___jp_225_:
{
if (v___y_226_ == 0)
{
lean_object* v_ks_227_; lean_object* v_vs_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_ks_227_ = lean_ctor_get(v_newNode_224_, 0);
lean_inc_ref(v_ks_227_);
v_vs_228_ = lean_ctor_get(v_newNode_224_, 1);
lean_inc_ref(v_vs_228_);
lean_dec_ref(v_newNode_224_);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_231_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_x_168_, v_ks_227_, v_vs_228_, v___x_229_, v___x_230_);
lean_dec_ref(v_vs_228_);
lean_dec_ref(v_ks_227_);
return v___x_231_;
}
else
{
return v_newNode_224_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(size_t v_depth_239_, lean_object* v_keys_240_, lean_object* v_vals_241_, lean_object* v_i_242_, lean_object* v_entries_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_array_get_size(v_keys_240_);
v___x_245_ = lean_nat_dec_lt(v_i_242_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_i_242_);
return v_entries_243_;
}
else
{
lean_object* v_k_246_; lean_object* v_v_247_; uint64_t v___y_249_; 
v_k_246_ = lean_array_fget_borrowed(v_keys_240_, v_i_242_);
v_v_247_ = lean_array_fget_borrowed(v_vals_241_, v_i_242_);
if (lean_obj_tag(v_k_246_) == 0)
{
uint64_t v___x_260_; 
v___x_260_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_249_ = v___x_260_;
goto v___jp_248_;
}
else
{
uint64_t v_hash_261_; 
v_hash_261_ = lean_ctor_get_uint64(v_k_246_, sizeof(void*)*2);
v___y_249_ = v_hash_261_;
goto v___jp_248_;
}
v___jp_248_:
{
size_t v_h_250_; size_t v___x_251_; lean_object* v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v_h_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_h_250_ = lean_uint64_to_usize(v___y_249_);
v___x_251_ = ((size_t)5ULL);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v_depth_239_, v___x_253_);
v___x_255_ = lean_usize_mul(v___x_251_, v___x_254_);
v_h_256_ = lean_usize_shift_right(v_h_250_, v___x_255_);
v___x_257_ = lean_nat_add(v_i_242_, v___x_252_);
lean_dec(v_i_242_);
lean_inc(v_v_247_);
lean_inc(v_k_246_);
v___x_258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_entries_243_, v_h_256_, v_depth_239_, v_k_246_, v_v_247_);
v_i_242_ = v___x_257_;
v_entries_243_ = v___x_258_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_262_, lean_object* v_keys_263_, lean_object* v_vals_264_, lean_object* v_i_265_, lean_object* v_entries_266_){
_start:
{
size_t v_depth_boxed_267_; lean_object* v_res_268_; 
v_depth_boxed_267_ = lean_unbox_usize(v_depth_262_);
lean_dec(v_depth_262_);
v_res_268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_boxed_267_, v_keys_263_, v_vals_264_, v_i_265_, v_entries_266_);
lean_dec_ref(v_vals_264_);
lean_dec_ref(v_keys_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___boxed(lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
size_t v_x_2078__boxed_274_; size_t v_x_2079__boxed_275_; lean_object* v_res_276_; 
v_x_2078__boxed_274_ = lean_unbox_usize(v_x_270_);
lean_dec(v_x_270_);
v_x_2079__boxed_275_ = lean_unbox_usize(v_x_271_);
lean_dec(v_x_271_);
v_res_276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_269_, v_x_2078__boxed_274_, v_x_2079__boxed_275_, v_x_272_, v_x_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
uint64_t v___y_281_; 
if (lean_obj_tag(v_x_278_) == 0)
{
uint64_t v___x_285_; 
v___x_285_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_281_ = v___x_285_;
goto v___jp_280_;
}
else
{
uint64_t v_hash_286_; 
v_hash_286_ = lean_ctor_get_uint64(v_x_278_, sizeof(void*)*2);
v___y_281_ = v_hash_286_;
goto v___jp_280_;
}
v___jp_280_:
{
size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_uint64_to_usize(v___y_281_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_277_, v___x_282_, v___x_283_, v_x_278_, v_x_279_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(lean_object* v_vs_287_, lean_object* v_v_288_, lean_object* v_i_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_vs_287_);
v___x_291_ = lean_nat_dec_lt(v_i_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec(v_i_289_);
v___x_292_ = lean_array_push(v_vs_287_, v_v_288_);
return v___x_292_;
}
else
{
lean_object* v_val_293_; lean_object* v___x_294_; lean_object* v_val_295_; uint8_t v___x_296_; 
v_val_293_ = lean_ctor_get(v_v_288_, 1);
v___x_294_ = lean_array_fget_borrowed(v_vs_287_, v_i_289_);
v_val_295_ = lean_ctor_get(v___x_294_, 1);
v___x_296_ = lean_expr_eqv(v_val_293_, v_val_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_289_, v___x_297_);
lean_dec(v_i_289_);
v_i_289_ = v___x_298_;
goto _start;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_array_fset(v_vs_287_, v_i_289_, v_v_288_);
lean_dec(v_i_289_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(lean_object* v_vs_301_, lean_object* v_v_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5_spec__12(v_vs_301_, v_v_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
lean_object* v_fst_307_; lean_object* v_fst_308_; uint8_t v___x_309_; 
v_fst_307_ = lean_ctor_get(v_a_305_, 0);
v_fst_308_ = lean_ctor_get(v_b_306_, 0);
v___x_309_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_307_, v_fst_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_a_310_, v_b_311_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_a_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_314_, lean_object* v_keys_315_, lean_object* v_v_316_, lean_object* v_k_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_c_321_; lean_object* v___x_322_; 
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_x_314_, v___x_319_);
v_c_321_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_315_, v_v_316_, v___x_320_);
lean_dec(v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_k_317_);
lean_ctor_set(v___x_322_, 1, v_c_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_323_, lean_object* v_keys_324_, lean_object* v_v_325_, lean_object* v_k_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_323_, v_keys_324_, v_v_325_, v_k_326_, v_x_327_);
lean_dec_ref(v_keys_324_);
lean_dec(v_x_323_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(lean_object* v_x_333_, lean_object* v_keys_334_, lean_object* v_v_335_, lean_object* v_k_336_, lean_object* v_as_337_, lean_object* v_k_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_mid_343_; lean_object* v_midVal_344_; uint8_t v___x_345_; 
v___x_341_ = lean_nat_add(v_x_339_, v_x_340_);
v___x_342_ = lean_unsigned_to_nat(1u);
v_mid_343_ = lean_nat_shiftr(v___x_341_, v___x_342_);
lean_dec(v___x_341_);
v_midVal_344_ = lean_array_fget(v_as_337_, v_mid_343_);
v___x_345_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_midVal_344_, v_k_338_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
lean_dec(v_x_340_);
v___x_346_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_338_, v_midVal_344_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
lean_dec(v_x_339_);
v___x_347_ = lean_array_get_size(v_as_337_);
v___x_348_ = lean_nat_dec_lt(v_mid_343_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v_midVal_344_);
lean_dec(v_mid_343_);
lean_dec(v_k_336_);
lean_dec_ref(v_v_335_);
return v_as_337_;
}
else
{
lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_361_; 
v_snd_349_ = lean_ctor_get(v_midVal_344_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_midVal_344_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v_midVal_344_, 0);
lean_dec(v_unused_362_);
v___x_351_ = v_midVal_344_;
v_isShared_352_ = v_isSharedCheck_361_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_dec(v_midVal_344_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_361_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v_xs_x27_354_; lean_object* v___x_355_; lean_object* v_c_356_; lean_object* v___x_358_; 
v___x_353_ = lean_box(0);
v_xs_x27_354_ = lean_array_fset(v_as_337_, v_mid_343_, v___x_353_);
v___x_355_ = lean_nat_add(v_x_333_, v___x_342_);
v_c_356_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_334_, v_v_335_, v___x_355_, v_snd_349_);
lean_dec(v___x_355_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_c_356_);
lean_ctor_set(v___x_351_, 0, v_k_336_);
v___x_358_ = v___x_351_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_k_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_c_356_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_array_fset(v_xs_x27_354_, v_mid_343_, v___x_358_);
lean_dec(v_mid_343_);
return v___x_359_;
}
}
}
}
else
{
lean_dec(v_midVal_344_);
v_x_340_ = v_mid_343_;
goto _start;
}
}
else
{
uint8_t v___x_364_; 
lean_dec(v_midVal_344_);
v___x_364_ = lean_nat_dec_eq(v_mid_343_, v_x_339_);
if (v___x_364_ == 0)
{
lean_dec(v_x_339_);
v_x_339_ = v_mid_343_;
goto _start;
}
else
{
lean_object* v___x_366_; lean_object* v_c_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_j_370_; lean_object* v_as_371_; lean_object* v___x_372_; 
lean_dec(v_mid_343_);
lean_dec(v_x_340_);
v___x_366_ = lean_nat_add(v_x_333_, v___x_342_);
v_c_367_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_334_, v_v_335_, v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_k_336_);
lean_ctor_set(v___x_368_, 1, v_c_367_);
v___x_369_ = lean_nat_add(v_x_339_, v___x_342_);
lean_dec(v_x_339_);
v_j_370_ = lean_array_get_size(v_as_337_);
v_as_371_ = lean_array_push(v_as_337_, v___x_368_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_369_, v_as_371_, v_j_370_);
lean_dec(v___x_369_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(lean_object* v_x_373_, lean_object* v_keys_374_, lean_object* v_v_375_, lean_object* v_k_376_, lean_object* v_as_377_, lean_object* v_k_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_379_ = lean_array_get_size(v_as_377_);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_nat_dec_eq(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_fget_borrowed(v_as_377_, v___x_380_);
v___x_383_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_378_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_382_, v_k_378_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_lt(v___x_380_, v___x_379_);
if (v___x_385_ == 0)
{
lean_dec(v_k_376_);
lean_dec_ref(v_v_375_);
return v_as_377_;
}
else
{
lean_object* v___x_386_; lean_object* v_xs_x27_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc(v___x_382_);
v___x_386_ = lean_box(0);
v_xs_x27_387_ = lean_array_fset(v_as_377_, v___x_380_, v___x_386_);
v___x_388_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v___x_382_);
v___x_389_ = lean_array_fset(v_xs_x27_387_, v___x_380_, v___x_388_);
return v___x_389_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_sub(v___x_379_, v___x_390_);
v___x_392_ = lean_array_fget_borrowed(v_as_377_, v___x_391_);
v___x_393_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v___x_392_, v_k_378_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__1(v_k_378_, v___x_392_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_lt(v___x_391_, v___x_379_);
if (v___x_395_ == 0)
{
lean_dec(v___x_391_);
lean_dec(v_k_376_);
lean_dec_ref(v_v_375_);
return v_as_377_;
}
else
{
lean_object* v___x_396_; lean_object* v_xs_x27_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v___x_392_);
v___x_396_ = lean_box(0);
v_xs_x27_397_ = lean_array_fset(v_as_377_, v___x_391_, v___x_396_);
v___x_398_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v___x_392_);
v___x_399_ = lean_array_fset(v_xs_x27_397_, v___x_391_, v___x_398_);
lean_dec(v___x_391_);
return v___x_399_;
}
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v_as_377_, v_k_378_, v___x_380_, v___x_391_);
return v___x_400_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v___x_391_);
v___x_401_ = lean_box(0);
v___x_402_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v___x_401_);
v___x_403_ = lean_array_push(v_as_377_, v___x_402_);
return v___x_403_;
}
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_as_406_; lean_object* v___x_407_; 
v___x_404_ = lean_box(0);
v___x_405_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v___x_404_);
v_as_406_ = lean_array_push(v_as_377_, v___x_405_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_380_, v_as_406_, v___x_379_);
return v___x_407_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_box(0);
v___x_409_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__0(v_x_373_, v_keys_374_, v_v_375_, v_k_376_, v___x_408_);
v___x_410_ = lean_array_push(v_as_377_, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_keys_411_, lean_object* v_v_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_vs_415_; lean_object* v_children_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_433_; 
v_vs_415_ = lean_ctor_get(v_x_414_, 0);
v_children_416_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_418_ = v_x_414_;
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_children_416_);
lean_inc(v_vs_415_);
lean_dec(v_x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_array_get_size(v_keys_411_);
v___x_421_ = lean_nat_dec_lt(v_x_413_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__5(v_vs_415_, v_v_412_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_422_);
v___x_424_ = v___x_418_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_children_416_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v_k_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_c_429_; lean_object* v___x_431_; 
v_k_426_ = lean_array_fget_borrowed(v_keys_411_, v_x_413_);
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1));
lean_inc_n(v_k_426_, 2);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_k_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v_c_429_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_413_, v_keys_411_, v_v_412_, v_k_426_, v_children_416_, v___x_428_);
lean_dec_ref(v___x_428_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_c_429_);
v___x_431_ = v___x_418_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_vs_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_c_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_434_, lean_object* v_keys_435_, lean_object* v_v_436_, lean_object* v_k_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_449_; 
v_snd_439_ = lean_ctor_get(v_x_438_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v_x_438_, 0);
lean_dec(v_unused_450_);
v___x_441_ = v_x_438_;
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_dec(v_x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_c_445_; lean_object* v___x_447_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_x_434_, v___x_443_);
v_c_445_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_435_, v_v_436_, v___x_444_, v_snd_439_);
lean_dec(v___x_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_c_445_);
lean_ctor_set(v___x_441_, 0, v_k_437_);
v___x_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_k_437_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_c_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_451_, lean_object* v_keys_452_, lean_object* v_v_453_, lean_object* v_k_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___lam__2(v_x_451_, v_keys_452_, v_v_453_, v_k_454_, v_x_455_);
lean_dec_ref(v_keys_452_);
lean_dec(v_x_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___boxed(lean_object* v_keys_457_, lean_object* v_v_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_457_, v_v_458_, v_x_459_, v_x_460_);
lean_dec(v_x_459_);
lean_dec_ref(v_keys_457_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_x_462_, lean_object* v_keys_463_, lean_object* v_v_464_, lean_object* v_k_465_, lean_object* v_as_466_, lean_object* v_k_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_462_, v_keys_463_, v_v_464_, v_k_465_, v_as_466_, v_k_467_, v_x_468_, v_x_469_);
lean_dec_ref(v_k_467_);
lean_dec_ref(v_keys_463_);
lean_dec(v_x_462_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6___boxed(lean_object* v_x_471_, lean_object* v_keys_472_, lean_object* v_v_473_, lean_object* v_k_474_, lean_object* v_as_475_, lean_object* v_k_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6(v_x_471_, v_keys_472_, v_v_473_, v_k_474_, v_as_475_, v_k_476_);
lean_dec_ref(v_k_476_);
lean_dec_ref(v_keys_472_);
lean_dec(v_x_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_i_480_, lean_object* v_k_481_){
_start:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_array_get_size(v_keys_478_);
v___x_483_ = lean_nat_dec_lt(v_i_480_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v_i_480_);
v___x_484_ = lean_box(0);
return v___x_484_;
}
else
{
lean_object* v_k_x27_485_; uint8_t v___x_486_; 
v_k_x27_485_ = lean_array_fget_borrowed(v_keys_478_, v_i_480_);
v___x_486_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_481_, v_k_x27_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_i_480_, v___x_487_);
lean_dec(v_i_480_);
v_i_480_ = v___x_488_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_array_fget_borrowed(v_vals_479_, v_i_480_);
lean_dec(v_i_480_);
lean_inc(v___x_490_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_492_, v_vals_493_, v_i_494_, v_k_495_);
lean_dec(v_k_495_);
lean_dec_ref(v_vals_493_);
lean_dec_ref(v_keys_492_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_497_, size_t v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
lean_object* v_es_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_521_; 
v_es_500_ = lean_ctor_get(v_x_497_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_521_ == 0)
{
v___x_502_ = v_x_497_;
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_es_500_);
lean_dec(v_x_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v_j_508_; lean_object* v___x_509_; 
v___x_504_ = lean_box(2);
v___x_505_ = ((size_t)5ULL);
v___x_506_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_507_ = lean_usize_land(v_x_498_, v___x_506_);
v_j_508_ = lean_usize_to_nat(v___x_507_);
v___x_509_ = lean_array_get(v___x_504_, v_es_500_, v_j_508_);
lean_dec(v_j_508_);
lean_dec_ref(v_es_500_);
switch(lean_obj_tag(v___x_509_))
{
case 0:
{
lean_object* v_key_510_; lean_object* v_val_511_; uint8_t v___x_512_; 
v_key_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_key_510_);
v_val_511_ = lean_ctor_get(v___x_509_, 1);
lean_inc(v_val_511_);
lean_dec_ref(v___x_509_);
v___x_512_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_499_, v_key_510_);
lean_dec(v_key_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_val_511_);
lean_del_object(v___x_502_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v___x_515_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 1);
lean_ctor_set(v___x_502_, 0, v_val_511_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_val_511_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
case 1:
{
lean_object* v_node_517_; size_t v___x_518_; 
lean_del_object(v___x_502_);
v_node_517_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_node_517_);
lean_dec_ref(v___x_509_);
v___x_518_ = lean_usize_shift_right(v_x_498_, v___x_505_);
v_x_497_ = v_node_517_;
v_x_498_ = v___x_518_;
goto _start;
}
default: 
{
lean_object* v___x_520_; 
lean_del_object(v___x_502_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
}
}
else
{
lean_object* v_ks_522_; lean_object* v_vs_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_ks_522_ = lean_ctor_get(v_x_497_, 0);
lean_inc_ref(v_ks_522_);
v_vs_523_ = lean_ctor_get(v_x_497_, 1);
lean_inc_ref(v_vs_523_);
lean_dec_ref(v_x_497_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_522_, v_vs_523_, v___x_524_, v_x_499_);
lean_dec_ref(v_vs_523_);
lean_dec_ref(v_ks_522_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
size_t v_x_2529__boxed_529_; lean_object* v_res_530_; 
v_x_2529__boxed_529_ = lean_unbox_usize(v_x_527_);
lean_dec(v_x_527_);
v_res_530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_526_, v_x_2529__boxed_529_, v_x_528_);
lean_dec(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
uint64_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_532_);
v___x_534_ = lean_uint64_to_usize(v___x_533_);
v___x_535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_531_, v___x_534_, v_x_532_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_536_, v_x_537_);
lean_dec(v_x_537_);
return v_res_538_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(lean_object* v_msg_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0);
v___x_542_ = lean_panic_fn_borrowed(v___x_541_, v_msg_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_ks_547_; lean_object* v_vs_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_572_; 
v_ks_547_ = lean_ctor_get(v_x_543_, 0);
v_vs_548_ = lean_ctor_get(v_x_543_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_572_ == 0)
{
v___x_550_ = v_x_543_;
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_vs_548_);
lean_inc(v_ks_547_);
lean_dec(v_x_543_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v_ks_547_);
v___x_553_ = lean_nat_dec_lt(v_x_544_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
lean_dec(v_x_544_);
v___x_554_ = lean_array_push(v_ks_547_, v_x_545_);
v___x_555_ = lean_array_push(v_vs_548_, v_x_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_555_);
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_557_ = v___x_550_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_object* v_k_x27_559_; uint8_t v___x_560_; 
v_k_x27_559_ = lean_array_fget_borrowed(v_ks_547_, v_x_544_);
v___x_560_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_545_, v_k_x27_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; 
if (v_isShared_551_ == 0)
{
v___x_562_ = v___x_550_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_ks_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_vs_548_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_x_544_, v___x_563_);
lean_dec(v_x_544_);
v_x_543_ = v___x_562_;
v_x_544_ = v___x_564_;
goto _start;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_array_fset(v_ks_547_, v_x_544_, v_x_545_);
v___x_568_ = lean_array_fset(v_vs_548_, v_x_544_, v_x_546_);
lean_dec(v_x_544_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_568_);
lean_ctor_set(v___x_550_, 0, v___x_567_);
v___x_570_ = v___x_550_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_n_573_, lean_object* v_k_574_, lean_object* v_v_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_n_573_, v___x_576_, v_k_574_, v_v_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_x_579_, size_t v_x_580_, size_t v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_es_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; size_t v___x_588_; lean_object* v_j_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_es_584_ = lean_ctor_get(v_x_579_, 0);
v___x_585_ = ((size_t)5ULL);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_588_ = lean_usize_land(v_x_580_, v___x_587_);
v_j_589_ = lean_usize_to_nat(v___x_588_);
v___x_590_ = lean_array_get_size(v_es_584_);
v___x_591_ = lean_nat_dec_lt(v_j_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v_j_589_);
lean_dec(v_x_583_);
lean_dec(v_x_582_);
return v_x_579_;
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_628_; 
lean_inc_ref(v_es_584_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_x_579_, 0);
lean_dec(v_unused_629_);
v___x_593_ = v_x_579_;
v_isShared_594_ = v_isSharedCheck_628_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_x_579_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_628_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_v_595_; lean_object* v___x_596_; lean_object* v_xs_x27_597_; lean_object* v___y_599_; 
v_v_595_ = lean_array_fget(v_es_584_, v_j_589_);
v___x_596_ = lean_box(0);
v_xs_x27_597_ = lean_array_fset(v_es_584_, v_j_589_, v___x_596_);
switch(lean_obj_tag(v_v_595_))
{
case 0:
{
lean_object* v_key_604_; lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_key_604_ = lean_ctor_get(v_v_595_, 0);
v_val_605_ = lean_ctor_get(v_v_595_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_v_595_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_inc(v_key_604_);
lean_dec(v_v_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_582_, v_key_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_607_);
v___x_610_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_604_, v_val_605_, v_x_582_, v_x_583_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
v___y_599_ = v___x_611_;
goto v___jp_598_;
}
else
{
lean_object* v___x_613_; 
lean_dec(v_val_605_);
lean_dec(v_key_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_x_583_);
lean_ctor_set(v___x_607_, 0, v_x_582_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_x_582_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_x_583_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_599_ = v___x_613_;
goto v___jp_598_;
}
}
}
}
case 1:
{
lean_object* v_node_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_node_616_ = lean_ctor_get(v_v_595_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v_v_595_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_node_616_);
lean_dec(v_v_595_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = lean_usize_shift_right(v_x_580_, v___x_585_);
v___x_621_ = lean_usize_add(v_x_581_, v___x_586_);
v___x_622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_node_616_, v___x_620_, v___x_621_, v_x_582_, v_x_583_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v___y_599_ = v___x_624_;
goto v___jp_598_;
}
}
}
default: 
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_x_582_);
lean_ctor_set(v___x_627_, 1, v_x_583_);
v___y_599_ = v___x_627_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_array_fset(v_xs_x27_597_, v_j_589_, v___y_599_);
lean_dec(v_j_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_600_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
else
{
lean_object* v_ks_630_; lean_object* v_vs_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_651_; 
v_ks_630_ = lean_ctor_get(v_x_579_, 0);
v_vs_631_ = lean_ctor_get(v_x_579_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_651_ == 0)
{
v___x_633_ = v_x_579_;
v_isShared_634_ = v_isSharedCheck_651_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_vs_631_);
lean_inc(v_ks_630_);
lean_dec(v_x_579_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_651_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_ks_630_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_vs_631_);
v___x_636_ = v_reuseFailAlloc_650_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v_newNode_637_; uint8_t v___y_639_; size_t v___x_645_; uint8_t v___x_646_; 
v_newNode_637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v___x_636_, v_x_582_, v_x_583_);
v___x_645_ = ((size_t)7ULL);
v___x_646_ = lean_usize_dec_le(v___x_645_, v_x_581_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_637_);
v___x_648_ = lean_unsigned_to_nat(4u);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
lean_dec(v___x_647_);
v___y_639_ = v___x_649_;
goto v___jp_638_;
}
else
{
v___y_639_ = v___x_646_;
goto v___jp_638_;
}
v___jp_638_:
{
if (v___y_639_ == 0)
{
lean_object* v_ks_640_; lean_object* v_vs_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_ks_640_ = lean_ctor_get(v_newNode_637_, 0);
lean_inc_ref(v_ks_640_);
v_vs_641_ = lean_ctor_get(v_newNode_637_, 1);
lean_inc_ref(v_vs_641_);
lean_dec_ref(v_newNode_637_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_x_581_, v_ks_640_, v_vs_641_, v___x_642_, v___x_643_);
lean_dec_ref(v_vs_641_);
lean_dec_ref(v_ks_640_);
return v___x_644_;
}
else
{
return v_newNode_637_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(size_t v_depth_652_, lean_object* v_keys_653_, lean_object* v_vals_654_, lean_object* v_i_655_, lean_object* v_entries_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_keys_653_);
v___x_658_ = lean_nat_dec_lt(v_i_655_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_i_655_);
return v_entries_656_;
}
else
{
lean_object* v_k_659_; lean_object* v_v_660_; uint64_t v___x_661_; size_t v_h_662_; size_t v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v_h_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_k_659_ = lean_array_fget_borrowed(v_keys_653_, v_i_655_);
v_v_660_ = lean_array_fget_borrowed(v_vals_654_, v_i_655_);
v___x_661_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_659_);
v_h_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = ((size_t)5ULL);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_sub(v_depth_652_, v___x_665_);
v___x_667_ = lean_usize_mul(v___x_663_, v___x_666_);
v_h_668_ = lean_usize_shift_right(v_h_662_, v___x_667_);
v___x_669_ = lean_nat_add(v_i_655_, v___x_664_);
lean_dec(v_i_655_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
v___x_670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_entries_656_, v_h_668_, v_depth_652_, v_k_659_, v_v_660_);
v_i_655_ = v___x_669_;
v_entries_656_ = v___x_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_i_675_, lean_object* v_entries_676_){
_start:
{
size_t v_depth_boxed_677_; lean_object* v_res_678_; 
v_depth_boxed_677_ = lean_unbox_usize(v_depth_672_);
lean_dec(v_depth_672_);
v_res_678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_boxed_677_, v_keys_673_, v_vals_674_, v_i_675_, v_entries_676_);
lean_dec_ref(v_vals_674_);
lean_dec_ref(v_keys_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
size_t v_x_2691__boxed_684_; size_t v_x_2692__boxed_685_; lean_object* v_res_686_; 
v_x_2691__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_x_2692__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_679_, v_x_2691__boxed_684_, v_x_2692__boxed_685_, v_x_682_, v_x_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint64_t v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_690_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_688_);
v___x_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_687_, v___x_691_, v___x_692_, v_x_688_, v_x_689_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_698_ = lean_unsigned_to_nat(23u);
v___x_699_ = lean_unsigned_to_nat(166u);
v___x_700_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_701_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_702_ = l_mkPanicMessageWithDecl(v___x_701_, v___x_700_, v___x_699_, v___x_698_, v___x_697_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_703_, lean_object* v_keys_704_, lean_object* v_v_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_array_get_size(v_keys_704_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v_k_710_; lean_object* v___x_711_; 
v___x_709_ = lean_box(0);
v_k_710_ = lean_array_get_borrowed(v___x_709_, v_keys_704_, v___x_707_);
lean_inc_ref(v_d_703_);
v___x_711_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_d_703_, v_k_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; lean_object* v_c_713_; lean_object* v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v_c_713_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_704_, v_v_705_, v___x_712_);
lean_inc(v_k_710_);
v___x_714_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_703_, v_k_710_, v_c_713_);
return v___x_714_;
}
else
{
lean_object* v_val_715_; lean_object* v___x_716_; lean_object* v_c_717_; lean_object* v___x_718_; 
v_val_715_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_715_);
lean_dec_ref(v___x_711_);
v___x_716_ = lean_unsigned_to_nat(1u);
v_c_717_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_704_, v_v_705_, v___x_716_, v_val_715_);
lean_inc(v_k_710_);
v___x_718_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_703_, v_k_710_, v_c_717_);
return v___x_718_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref(v_v_705_);
lean_dec_ref(v_d_703_);
v___x_719_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_720_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_721_, lean_object* v_keys_722_, lean_object* v_v_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_721_, v_keys_722_, v_v_723_);
lean_dec_ref(v_keys_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(lean_object* v_xs_725_, lean_object* v_v_726_, lean_object* v_i_727_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_xs_725_);
v___x_729_ = lean_nat_dec_lt(v_i_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v_i_727_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_fget_borrowed(v_xs_725_, v_i_727_);
v___x_732_ = lean_name_eq(v___x_731_, v_v_726_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_add(v_i_727_, v___x_733_);
lean_dec(v_i_727_);
v_i_727_ = v___x_734_;
goto _start;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_i_727_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21___boxed(lean_object* v_xs_737_, lean_object* v_v_738_, lean_object* v_i_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_737_, v_v_738_, v_i_739_);
lean_dec(v_v_738_);
lean_dec_ref(v_xs_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(lean_object* v_xs_741_, lean_object* v_v_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_741_, v_v_742_, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14___boxed(lean_object* v_xs_745_, lean_object* v_v_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_xs_745_, v_v_746_);
lean_dec(v_v_746_);
lean_dec_ref(v_xs_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(lean_object* v_x_748_, size_t v_x_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_es_751_; lean_object* v___x_752_; size_t v___x_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v_j_756_; lean_object* v_entry_757_; 
v_es_751_ = lean_ctor_get(v_x_748_, 0);
v___x_752_ = lean_box(2);
v___x_753_ = ((size_t)5ULL);
v___x_754_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_755_ = lean_usize_land(v_x_749_, v___x_754_);
v_j_756_ = lean_usize_to_nat(v___x_755_);
v_entry_757_ = lean_array_get(v___x_752_, v_es_751_, v_j_756_);
switch(lean_obj_tag(v_entry_757_))
{
case 0:
{
lean_object* v_key_758_; uint8_t v___x_759_; 
v_key_758_ = lean_ctor_get(v_entry_757_, 0);
lean_inc(v_key_758_);
lean_dec_ref(v_entry_757_);
v___x_759_ = lean_name_eq(v_x_750_, v_key_758_);
lean_dec(v_key_758_);
if (v___x_759_ == 0)
{
lean_dec(v_j_756_);
return v_x_748_;
}
else
{
lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
lean_inc_ref(v_es_751_);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_x_748_, 0);
lean_dec(v_unused_768_);
v___x_761_ = v_x_748_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_dec(v_x_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_array_set(v_es_751_, v_j_756_, v___x_752_);
lean_dec(v_j_756_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
case 1:
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_802_; 
lean_inc_ref(v_es_751_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_x_748_, 0);
lean_dec(v_unused_803_);
v___x_770_ = v_x_748_;
v_isShared_771_ = v_isSharedCheck_802_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_x_748_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_802_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_node_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_801_; 
v_node_772_ = lean_ctor_get(v_entry_757_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_entry_757_);
if (v_isSharedCheck_801_ == 0)
{
v___x_774_ = v_entry_757_;
v_isShared_775_ = v_isSharedCheck_801_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_node_772_);
lean_dec(v_entry_757_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_801_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_entries_776_; size_t v___x_777_; lean_object* v_newNode_778_; lean_object* v___x_779_; 
v_entries_776_ = lean_array_set(v_es_751_, v_j_756_, v___x_752_);
v___x_777_ = lean_usize_shift_right(v_x_749_, v___x_753_);
v_newNode_778_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_node_772_, v___x_777_, v_x_750_);
lean_inc_ref(v_newNode_778_);
v___x_779_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_781_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_newNode_778_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_newNode_778_);
v___x_781_ = v_reuseFailAlloc_786_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_array_set(v_entries_776_, v_j_756_, v___x_781_);
lean_dec(v_j_756_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_782_);
v___x_784_ = v___x_770_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_val_787_; lean_object* v_fst_788_; lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_newNode_778_);
lean_del_object(v___x_774_);
v_val_787_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_787_);
lean_dec_ref(v___x_779_);
v_fst_788_ = lean_ctor_get(v_val_787_, 0);
v_snd_789_ = lean_ctor_get(v_val_787_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_val_787_);
if (v_isSharedCheck_800_ == 0)
{
v___x_791_ = v_val_787_;
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_inc(v_fst_788_);
lean_dec(v_val_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_fst_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_789_);
v___x_794_ = v_reuseFailAlloc_799_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = lean_array_set(v_entries_776_, v_j_756_, v___x_794_);
lean_dec(v_j_756_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_795_);
v___x_797_ = v___x_770_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_756_);
return v_x_748_;
}
}
}
else
{
lean_object* v_ks_804_; lean_object* v_vs_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_819_; 
v_ks_804_ = lean_ctor_get(v_x_748_, 0);
v_vs_805_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_819_ == 0)
{
v___x_807_ = v_x_748_;
v_isShared_808_ = v_isSharedCheck_819_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_vs_805_);
lean_inc(v_ks_804_);
lean_dec(v_x_748_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_819_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; 
v___x_809_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_ks_804_, v_x_750_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_811_; 
if (v_isShared_808_ == 0)
{
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_ks_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_vs_805_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_val_813_; lean_object* v_keys_x27_814_; lean_object* v_vals_x27_815_; lean_object* v___x_817_; 
v_val_813_ = lean_ctor_get(v___x_809_, 0);
lean_inc_n(v_val_813_, 2);
lean_dec_ref(v___x_809_);
v_keys_x27_814_ = l_Array_eraseIdx___redArg(v_ks_804_, v_val_813_);
v_vals_x27_815_ = l_Array_eraseIdx___redArg(v_vs_805_, v_val_813_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_vals_x27_815_);
lean_ctor_set(v___x_807_, 0, v_keys_x27_814_);
v___x_817_ = v___x_807_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_keys_x27_814_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_vals_x27_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg___boxed(lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_2940__boxed_823_; lean_object* v_res_824_; 
v_x_2940__boxed_823_ = lean_unbox_usize(v_x_821_);
lean_dec(v_x_821_);
v_res_824_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_820_, v_x_2940__boxed_823_, v_x_822_);
lean_dec(v_x_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
uint64_t v___y_828_; 
if (lean_obj_tag(v_x_826_) == 0)
{
uint64_t v___x_831_; 
v___x_831_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_828_ = v___x_831_;
goto v___jp_827_;
}
else
{
uint64_t v_hash_832_; 
v_hash_832_ = lean_ctor_get_uint64(v_x_826_, sizeof(void*)*2);
v___y_828_ = v_hash_832_;
goto v___jp_827_;
}
v___jp_827_:
{
size_t v_h_829_; lean_object* v___x_830_; 
v_h_829_ = lean_uint64_to_usize(v___y_828_);
v___x_830_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_825_, v_h_829_, v_x_826_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_833_, v_x_834_);
lean_dec(v_x_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_836_, lean_object* v_e_837_){
_start:
{
lean_object* v_globalName_x3f_838_; 
v_globalName_x3f_838_ = lean_ctor_get(v_e_837_, 3);
if (lean_obj_tag(v_globalName_x3f_838_) == 0)
{
lean_object* v_keys_839_; lean_object* v_discrTree_840_; lean_object* v_instanceNames_841_; lean_object* v_erased_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_keys_839_ = lean_ctor_get(v_e_837_, 0);
lean_inc_ref(v_keys_839_);
v_discrTree_840_ = lean_ctor_get(v_d_836_, 0);
v_instanceNames_841_ = lean_ctor_get(v_d_836_, 1);
v_erased_842_ = lean_ctor_get(v_d_836_, 2);
v_isSharedCheck_850_ = !lean_is_exclusive(v_d_836_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v_d_836_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_erased_842_);
lean_inc(v_instanceNames_841_);
lean_inc(v_discrTree_840_);
lean_dec(v_d_836_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_840_, v_keys_839_, v_e_837_);
lean_dec_ref(v_keys_839_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_instanceNames_841_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_erased_842_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_keys_851_; lean_object* v_val_852_; lean_object* v_discrTree_853_; lean_object* v_instanceNames_854_; lean_object* v_erased_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_keys_851_ = lean_ctor_get(v_e_837_, 0);
v_val_852_ = lean_ctor_get(v_globalName_x3f_838_, 0);
lean_inc(v_val_852_);
v_discrTree_853_ = lean_ctor_get(v_d_836_, 0);
v_instanceNames_854_ = lean_ctor_get(v_d_836_, 1);
v_erased_855_ = lean_ctor_get(v_d_836_, 2);
v_isSharedCheck_865_ = !lean_is_exclusive(v_d_836_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v_d_836_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_erased_855_);
lean_inc(v_instanceNames_854_);
lean_inc(v_discrTree_853_);
lean_dec(v_d_836_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_inc_ref(v_e_837_);
v___x_859_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_853_, v_keys_851_, v_e_837_);
lean_inc(v_val_852_);
v___x_860_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_854_, v_val_852_, v_e_837_);
v___x_861_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_855_, v_val_852_);
lean_dec(v_val_852_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 2, v___x_861_);
lean_ctor_set(v___x_857_, 1, v___x_860_);
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec(v_x_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_00_u03b2_883_, v_x_884_, v_x_885_);
lean_dec(v_x_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, size_t v_x_894_, size_t v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___boxed(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_3165__boxed_905_; size_t v_x_3166__boxed_906_; lean_object* v_res_907_; 
v_x_3165__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_3166__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(v_00_u03b2_899_, v_x_900_, v_x_3165__boxed_905_, v_x_3166__boxed_906_, v_x_903_, v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, size_t v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_909_, v_x_910_, v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___boxed(lean_object* v_00_u03b2_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
size_t v_x_3182__boxed_917_; lean_object* v_res_918_; 
v_x_3182__boxed_917_ = lean_unbox_usize(v_x_915_);
lean_dec(v_x_915_);
v_res_918_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(v_00_u03b2_913_, v_x_914_, v_x_3182__boxed_917_, v_x_916_);
lean_dec(v_x_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, size_t v_x_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_920_, v_x_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
size_t v_x_3193__boxed_928_; lean_object* v_res_929_; 
v_x_3193__boxed_928_ = lean_unbox_usize(v_x_926_);
lean_dec(v_x_926_);
v_res_929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_00_u03b2_924_, v_x_925_, v_x_3193__boxed_928_, v_x_927_);
lean_dec(v_x_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, size_t v_x_932_, size_t v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_931_, v_x_932_, v_x_933_, v_x_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
size_t v_x_3204__boxed_943_; size_t v_x_3205__boxed_944_; lean_object* v_res_945_; 
v_x_3204__boxed_943_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_x_3205__boxed_944_ = lean_unbox_usize(v_x_940_);
lean_dec(v_x_940_);
v_res_945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(v_00_u03b2_937_, v_x_938_, v_x_3204__boxed_943_, v_x_3205__boxed_944_, v_x_941_, v_x_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_946_, lean_object* v_n_947_, lean_object* v_k_948_, lean_object* v_v_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v_n_947_, v_k_948_, v_v_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_951_, size_t v_depth_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_heq_955_, lean_object* v_i_956_, lean_object* v_entries_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_952_, v_keys_953_, v_vals_954_, v_i_956_, v_entries_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_959_, lean_object* v_depth_960_, lean_object* v_keys_961_, lean_object* v_vals_962_, lean_object* v_heq_963_, lean_object* v_i_964_, lean_object* v_entries_965_){
_start:
{
size_t v_depth_boxed_966_; lean_object* v_res_967_; 
v_depth_boxed_966_ = lean_unbox_usize(v_depth_960_);
lean_dec(v_depth_960_);
v_res_967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(v_00_u03b2_959_, v_depth_boxed_966_, v_keys_961_, v_vals_962_, v_heq_963_, v_i_964_, v_entries_965_);
lean_dec_ref(v_vals_962_);
lean_dec_ref(v_keys_961_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_968_, lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_heq_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_969_, v_vals_970_, v_i_972_, v_k_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_975_, lean_object* v_keys_976_, lean_object* v_vals_977_, lean_object* v_heq_978_, lean_object* v_i_979_, lean_object* v_k_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_975_, v_keys_976_, v_vals_977_, v_heq_978_, v_i_979_, v_k_980_);
lean_dec(v_k_980_);
lean_dec_ref(v_vals_977_);
lean_dec_ref(v_keys_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_982_, lean_object* v_n_983_, lean_object* v_k_984_, lean_object* v_v_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v_n_983_, v_k_984_, v_v_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_987_, size_t v_depth_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_entries_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_988_, v_keys_989_, v_vals_990_, v_i_992_, v_entries_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_995_, lean_object* v_depth_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_entries_1001_){
_start:
{
size_t v_depth_boxed_1002_; lean_object* v_res_1003_; 
v_depth_boxed_1002_ = lean_unbox_usize(v_depth_996_);
lean_dec(v_depth_996_);
v_res_1003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_995_, v_depth_boxed_1002_, v_keys_997_, v_vals_998_, v_heq_999_, v_i_1000_, v_entries_1001_);
lean_dec_ref(v_vals_998_);
lean_dec_ref(v_keys_997_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(lean_object* v_x_1004_, lean_object* v_keys_1005_, lean_object* v_v_1006_, lean_object* v_k_1007_, lean_object* v_as_1008_, lean_object* v_k_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_1004_, v_keys_1005_, v_v_1006_, v_k_1007_, v_as_1008_, v_k_1009_, v_x_1010_, v_x_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___boxed(lean_object* v_x_1015_, lean_object* v_keys_1016_, lean_object* v_v_1017_, lean_object* v_k_1018_, lean_object* v_as_1019_, lean_object* v_k_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(v_x_1015_, v_keys_1016_, v_v_1017_, v_k_1018_, v_as_1019_, v_k_1020_, v_x_1021_, v_x_1022_, v_x_1023_, v_x_1024_);
lean_dec_ref(v_k_1020_);
lean_dec_ref(v_keys_1016_);
lean_dec(v_x_1015_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_x_1027_, v_x_1028_, v_x_1029_, v_x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1033_, v_x_1034_, v_x_1035_, v_x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1038_, lean_object* v_declName_1039_){
_start:
{
lean_object* v_discrTree_1040_; lean_object* v_instanceNames_1041_; lean_object* v_erased_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v_discrTree_1040_ = lean_ctor_get(v_d_1038_, 0);
v_instanceNames_1041_ = lean_ctor_get(v_d_1038_, 1);
v_erased_1042_ = lean_ctor_get(v_d_1038_, 2);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_d_1038_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1044_ = v_d_1038_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_erased_1042_);
lean_inc(v_instanceNames_1041_);
lean_inc(v_discrTree_1040_);
lean_dec(v_d_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1046_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1041_, v_declName_1039_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1042_, v_declName_1039_, v___x_1047_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 2, v___x_1048_);
lean_ctor_set(v___x_1044_, 1, v___x_1046_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_discrTree_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1053_, lean_object* v_declName_1054_, lean_object* v_toPure_1055_, lean_object* v_____r_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l_Lean_Meta_Instances_eraseCore(v_d_1053_, v_declName_1054_);
v___x_1058_ = lean_apply_2(v_toPure_1055_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1059_, lean_object* v_____r_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_apply_1(v___f_1059_, v_____r_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_d_1072_, lean_object* v_declName_1073_){
_start:
{
lean_object* v_toApplicative_1074_; lean_object* v_toBind_1075_; lean_object* v_toPure_1076_; lean_object* v_instanceNames_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; uint8_t v___x_1081_; 
v_toApplicative_1074_ = lean_ctor_get(v_inst_1070_, 0);
v_toBind_1075_ = lean_ctor_get(v_inst_1070_, 1);
lean_inc(v_toBind_1075_);
v_toPure_1076_ = lean_ctor_get(v_toApplicative_1074_, 1);
v_instanceNames_1077_ = lean_ctor_get(v_d_1072_, 1);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1079_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1076_);
lean_inc_n(v_declName_1073_, 2);
lean_inc_ref(v_d_1072_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1080_, 0, v_d_1072_);
lean_closure_set(v___f_1080_, 1, v_declName_1073_);
lean_closure_set(v___f_1080_, 2, v_toPure_1076_);
lean_inc_ref(v_instanceNames_1077_);
v___x_1081_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1078_, v___x_1079_, v_instanceNames_1077_, v_declName_1073_);
if (v___x_1081_ == 0)
{
lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_d_1072_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1082_, 0, v___f_1080_);
v___x_1083_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1084_ = l_Lean_MessageData_ofConstName(v_declName_1073_, v___x_1081_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_throwError___redArg(v_inst_1070_, v_inst_1071_, v___x_1087_);
v___x_1089_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v___x_1088_, v___f_1082_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc(v_toPure_1076_);
lean_dec_ref(v___f_1080_);
lean_dec(v_toBind_1075_);
lean_dec_ref(v_inst_1071_);
lean_dec_ref(v_inst_1070_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1072_, v_declName_1073_, v_toPure_1076_, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_d_1095_, lean_object* v_declName_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1093_, v_inst_1094_, v_d_1095_, v_declName_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t v_level_1098_, lean_object* v_e_1099_){
_start:
{
uint8_t v___y_1101_; uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 2;
v___x_1105_ = l_Lean_instDecidableEqOLeanLevel(v_level_1098_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v_globalName_x3f_1106_; 
v_globalName_x3f_1106_ = lean_ctor_get(v_e_1099_, 3);
lean_inc(v_globalName_x3f_1106_);
if (lean_obj_tag(v_globalName_x3f_1106_) == 0)
{
v___y_1101_ = v___x_1105_;
goto v___jp_1100_;
}
else
{
lean_object* v_val_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1115_; 
v_val_1107_ = lean_ctor_get(v_globalName_x3f_1106_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_globalName_x3f_1106_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1109_ = v_globalName_x3f_1106_;
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_val_1107_);
lean_dec(v_globalName_x3f_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_isPrivateName(v_val_1107_);
lean_dec(v_val_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1113_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_e_1099_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_e_1099_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_del_object(v___x_1109_);
v___y_1101_ = v___x_1105_;
goto v___jp_1100_;
}
}
}
}
else
{
v___y_1101_ = v___x_1105_;
goto v___jp_1100_;
}
v___jp_1100_:
{
if (v___y_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref(v_e_1099_);
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_e_1099_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_level_1116_, lean_object* v_e_1117_){
_start:
{
uint8_t v_level_boxed_1118_; lean_object* v_res_1119_; 
v_level_boxed_1118_ = lean_unbox(v_level_1116_);
v_res_1119_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v_level_boxed_1118_, v_e_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object* v___y_1120_){
_start:
{
lean_inc_ref(v___y_1120_);
return v___y_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v___y_1121_);
lean_dec_ref(v___y_1121_);
return v_res_1122_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_1136_ = lean_obj_once(&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1137_ = lean_obj_once(&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1136_);
lean_ctor_set(v___x_1138_, 2, v___x_1135_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___f_1139_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___f_1140_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1141_ = lean_obj_once(&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1142_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1143_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v___x_1142_);
lean_ctor_set(v___x_1144_, 2, v___x_1141_);
lean_ctor_set(v___x_1144_, 3, v___f_1140_);
lean_ctor_set(v___x_1144_, 4, v___f_1139_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1147_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1150_, uint8_t v_allowLevelAssignments_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1151_, v_k_1150_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1157_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1157_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1174_, lean_object* v_allowLevelAssignments_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1181_; lean_object* v_res_1182_; 
v_allowLevelAssignments_boxed_1181_ = lean_unbox(v_allowLevelAssignments_1175_);
v_res_1182_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1174_, v_allowLevelAssignments_boxed_1181_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1183_, lean_object* v_k_1184_, uint8_t v_allowLevelAssignments_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1184_, v_allowLevelAssignments_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_k_1193_, lean_object* v_allowLevelAssignments_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1200_; lean_object* v_res_1201_; 
v_allowLevelAssignments_boxed_1200_ = lean_unbox(v_allowLevelAssignments_1194_);
v_res_1201_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1192_, v_k_1193_, v_allowLevelAssignments_boxed_1200_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1202_, lean_object* v___x_1203_, uint8_t v___x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1202_, v___x_1203_, v___x_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v_snd_1212_; lean_object* v_snd_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v_snd_1212_ = lean_ctor_get(v_a_1211_, 1);
lean_inc(v_snd_1212_);
lean_dec(v_a_1211_);
v_snd_1213_ = lean_ctor_get(v_snd_1212_, 1);
lean_inc(v_snd_1213_);
lean_dec(v_snd_1212_);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1213_, v___x_1214_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
v_a_1216_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1210_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1210_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_497__boxed_1232_; lean_object* v_res_1233_; 
v___x_497__boxed_1232_ = lean_unbox(v___x_1226_);
v_res_1233_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1224_, v___x_1225_, v___x_497__boxed_1232_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1240_; 
lean_inc(v_a_1238_);
lean_inc_ref(v_a_1237_);
lean_inc(v_a_1236_);
lean_inc_ref(v_a_1235_);
v___x_1240_ = lean_infer_type(v_e_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_box(0);
v___x_1243_ = 0;
v___x_1244_ = lean_box(v___x_1243_);
v___f_1245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1245_, 0, v_a_1241_);
lean_closure_set(v___f_1245_, 1, v___x_1242_);
lean_closure_set(v___f_1245_, 2, v___x_1244_);
v___x_1246_ = 0;
v___x_1247_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1245_, v___x_1246_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
return v___x_1247_;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1240_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1263_, lean_object* v_b_1264_, lean_object* v_c_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
v___x_1271_ = lean_apply_7(v_k_1263_, v_b_1264_, v_c_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1272_, lean_object* v_b_1273_, lean_object* v_c_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1272_, v_b_1273_, v_c_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1281_, lean_object* v_k_1282_, uint8_t v_cleanupAnnotations_1283_, uint8_t v_whnfType_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___f_1290_; lean_object* v___x_1291_; 
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1290_, 0, v_k_1282_);
v___x_1291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1281_, v___f_1290_, v_cleanupAnnotations_1283_, v_whnfType_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1291_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1291_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1308_, lean_object* v_k_1309_, lean_object* v_cleanupAnnotations_1310_, lean_object* v_whnfType_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1317_; uint8_t v_whnfType_boxed_1318_; lean_object* v_res_1319_; 
v_cleanupAnnotations_boxed_1317_ = lean_unbox(v_cleanupAnnotations_1310_);
v_whnfType_boxed_1318_ = lean_unbox(v_whnfType_1311_);
v_res_1319_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1308_, v_k_1309_, v_cleanupAnnotations_boxed_1317_, v_whnfType_boxed_1318_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1320_, lean_object* v_type_1321_, lean_object* v_k_1322_, uint8_t v_cleanupAnnotations_1323_, uint8_t v_whnfType_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1321_, v_k_1322_, v_cleanupAnnotations_1323_, v_whnfType_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1331_, lean_object* v_type_1332_, lean_object* v_k_1333_, lean_object* v_cleanupAnnotations_1334_, lean_object* v_whnfType_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1341_; uint8_t v_whnfType_boxed_1342_; lean_object* v_res_1343_; 
v_cleanupAnnotations_boxed_1341_ = lean_unbox(v_cleanupAnnotations_1334_);
v_whnfType_boxed_1342_ = lean_unbox(v_whnfType_1335_);
v_res_1343_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1331_, v_type_1332_, v_k_1333_, v_cleanupAnnotations_boxed_1341_, v_whnfType_boxed_1342_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1347_, size_t v_sz_1348_, size_t v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_usize_dec_lt(v_i_1349_, v_sz_1348_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_b_1350_);
return v___x_1357_;
}
else
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1411_; 
v_fst_1358_ = lean_ctor_get(v_b_1350_, 0);
v_snd_1359_ = lean_ctor_get(v_b_1350_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_b_1350_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1361_ = v_b_1350_;
v_isShared_1362_ = v_isSharedCheck_1411_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1358_);
lean_dec(v_b_1350_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1411_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_next_1368_; 
v_next_1368_ = lean_ctor_get(v_snd_1359_, 0);
lean_inc(v_next_1368_);
if (lean_obj_tag(v_next_1368_) == 0)
{
goto v___jp_1363_;
}
else
{
lean_object* v_upperBound_1369_; lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1410_; 
v_upperBound_1369_ = lean_ctor_get(v_snd_1359_, 1);
v_val_1370_ = lean_ctor_get(v_next_1368_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_next_1368_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1372_ = v_next_1368_;
v_isShared_1373_ = v_isSharedCheck_1410_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v_next_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1410_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_lt(v_val_1370_, v_upperBound_1369_);
if (v___x_1374_ == 0)
{
lean_del_object(v___x_1372_);
lean_dec(v_val_1370_);
goto v___jp_1363_;
}
else
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1407_; 
lean_inc(v_upperBound_1369_);
lean_del_object(v___x_1361_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_snd_1359_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; 
v_unused_1408_ = lean_ctor_get(v_snd_1359_, 1);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_snd_1359_, 0);
lean_dec(v_unused_1409_);
v___x_1376_ = v_snd_1359_;
v_isShared_1377_ = v_isSharedCheck_1407_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_snd_1359_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1407_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_array_uget_borrowed(v_as_1347_, v_i_1349_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v_a_1378_);
v___x_1379_ = lean_infer_type(v_a_1378_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_a_1382_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_val_1370_, v___x_1386_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1387_);
v___x_1389_ = v___x_1372_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1388_;
}
v___jp_1381_:
{
size_t v___x_1383_; size_t v___x_1384_; 
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_add(v_i_1349_, v___x_1383_);
v_i_1349_ = v___x_1384_;
v_b_1350_ = v_a_1382_;
goto _start;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1389_);
v___x_1391_ = v___x_1376_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_upperBound_1369_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1393_ = l_Lean_Expr_isAppOf(v_a_1380_, v___x_1392_);
lean_dec(v_a_1380_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_val_1370_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_fst_1358_);
lean_ctor_set(v___x_1394_, 1, v___x_1391_);
v_a_1382_ = v___x_1394_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_array_push(v_fst_1358_, v_val_1370_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___x_1391_);
v_a_1382_ = v___x_1396_;
goto v___jp_1381_;
}
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1376_);
lean_del_object(v___x_1372_);
lean_dec(v_val_1370_);
lean_dec(v_upperBound_1369_);
lean_dec(v_fst_1358_);
v_a_1399_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1379_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1379_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
v___jp_1363_:
{
lean_object* v___x_1365_; 
if (v_isShared_1362_ == 0)
{
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1359_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1412_, lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1412_, v_sz_boxed_1421_, v_i_boxed_1422_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_as_1412_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1428_, lean_object* v_args_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v___y_1438_; lean_object* v_env_1463_; lean_object* v___x_1464_; 
v___x_1436_ = lean_st_ref_get(v___y_1434_);
v_env_1463_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1463_);
lean_dec(v___x_1436_);
v___x_1464_ = l_Lean_getOutParamPositions_x3f(v_env_1463_, v_declName_1428_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1438_ = v___x_1465_;
goto v___jp_1437_;
}
else
{
lean_object* v_val_1466_; 
v_val_1466_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v___x_1464_);
v___y_1438_ = v_val_1466_;
goto v___jp_1437_;
}
v___jp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; size_t v_sz_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v___x_1439_ = lean_array_get_size(v_args_1429_);
v___x_1440_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___y_1438_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v_sz_1443_ = lean_array_size(v_args_1429_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1429_, v_sz_1443_, v___x_1444_, v___x_1442_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1454_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_fst_1450_; lean_object* v___x_1452_; 
v_fst_1450_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_fst_1450_);
lean_dec(v_a_1446_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v_fst_1450_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_fst_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_a_1455_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1445_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1445_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1467_, lean_object* v_args_1468_, lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1467_, v_args_1468_, v_x_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec_ref(v_x_1469_);
lean_dec_ref(v_args_1468_);
lean_dec(v_declName_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Expr_getAppFn(v_classTy_1476_);
if (lean_obj_tag(v___x_1482_) == 4)
{
lean_object* v_declName_1483_; lean_object* v___x_1484_; 
v_declName_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_declName_1483_);
lean_inc(v_a_1480_);
lean_inc_ref(v_a_1479_);
lean_inc(v_a_1478_);
lean_inc_ref(v_a_1477_);
v___x_1484_ = lean_infer_type(v___x_1482_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___f_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___f_1486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1486_, 0, v_declName_1483_);
v___x_1487_ = 0;
v___x_1488_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1485_, v___f_1486_, v___x_1487_, v___x_1487_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_declName_1483_);
v_a_1489_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1484_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1484_);
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
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref(v___x_1482_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec_ref(v_classTy_1499_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v_ks_1510_; lean_object* v_vs_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1535_; 
v_ks_1510_ = lean_ctor_get(v_x_1506_, 0);
v_vs_1511_ = lean_ctor_get(v_x_1506_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1513_ = v_x_1506_;
v_isShared_1514_ = v_isSharedCheck_1535_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_vs_1511_);
lean_inc(v_ks_1510_);
lean_dec(v_x_1506_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1535_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_array_get_size(v_ks_1510_);
v___x_1516_ = lean_nat_dec_lt(v_x_1507_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v_x_1507_);
v___x_1517_ = lean_array_push(v_ks_1510_, v_x_1508_);
v___x_1518_ = lean_array_push(v_vs_1511_, v_x_1509_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___x_1518_);
lean_ctor_set(v___x_1513_, 0, v___x_1517_);
v___x_1520_ = v___x_1513_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
else
{
lean_object* v_k_x27_1522_; uint8_t v___x_1523_; 
v_k_x27_1522_ = lean_array_fget_borrowed(v_ks_1510_, v_x_1507_);
v___x_1523_ = l_Lean_instBEqMVarId_beq(v_x_1508_, v_k_x27_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1525_; 
if (v_isShared_1514_ == 0)
{
v___x_1525_ = v___x_1513_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_ks_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_vs_1511_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_x_1507_, v___x_1526_);
lean_dec(v_x_1507_);
v_x_1506_ = v___x_1525_;
v_x_1507_ = v___x_1527_;
goto _start;
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1530_ = lean_array_fset(v_ks_1510_, v_x_1507_, v_x_1508_);
v___x_1531_ = lean_array_fset(v_vs_1511_, v_x_1507_, v_x_1509_);
lean_dec(v_x_1507_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___x_1531_);
lean_ctor_set(v___x_1513_, 0, v___x_1530_);
v___x_1533_ = v___x_1513_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_1536_, lean_object* v_k_1537_, lean_object* v_v_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_1536_, v___x_1539_, v_k_1537_, v_v_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1541_, size_t v_x_1542_, size_t v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_){
_start:
{
if (lean_obj_tag(v_x_1541_) == 0)
{
lean_object* v_es_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v_j_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_es_1546_ = lean_ctor_get(v_x_1541_, 0);
v___x_1547_ = ((size_t)5ULL);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_1550_ = lean_usize_land(v_x_1542_, v___x_1549_);
v_j_1551_ = lean_usize_to_nat(v___x_1550_);
v___x_1552_ = lean_array_get_size(v_es_1546_);
v___x_1553_ = lean_nat_dec_lt(v_j_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec(v_j_1551_);
lean_dec(v_x_1545_);
lean_dec(v_x_1544_);
return v_x_1541_;
}
else
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1590_; 
lean_inc_ref(v_es_1546_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1541_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v_x_1541_, 0);
lean_dec(v_unused_1591_);
v___x_1555_ = v_x_1541_;
v_isShared_1556_ = v_isSharedCheck_1590_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v_x_1541_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1590_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_v_1557_; lean_object* v___x_1558_; lean_object* v_xs_x27_1559_; lean_object* v___y_1561_; 
v_v_1557_ = lean_array_fget(v_es_1546_, v_j_1551_);
v___x_1558_ = lean_box(0);
v_xs_x27_1559_ = lean_array_fset(v_es_1546_, v_j_1551_, v___x_1558_);
switch(lean_obj_tag(v_v_1557_))
{
case 0:
{
lean_object* v_key_1566_; lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1577_; 
v_key_1566_ = lean_ctor_get(v_v_1557_, 0);
v_val_1567_ = lean_ctor_get(v_v_1557_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_v_1557_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1569_ = v_v_1557_;
v_isShared_1570_ = v_isSharedCheck_1577_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_inc(v_key_1566_);
lean_dec(v_v_1557_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1577_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_instBEqMVarId_beq(v_x_1544_, v_key_1566_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_del_object(v___x_1569_);
v___x_1572_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1566_, v_val_1567_, v_x_1544_, v_x_1545_);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
v___y_1561_ = v___x_1573_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1575_; 
lean_dec(v_val_1567_);
lean_dec(v_key_1566_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_x_1545_);
lean_ctor_set(v___x_1569_, 0, v_x_1544_);
v___x_1575_ = v___x_1569_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_x_1544_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_x_1545_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v___y_1561_ = v___x_1575_;
goto v___jp_1560_;
}
}
}
}
case 1:
{
lean_object* v_node_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1588_; 
v_node_1578_ = lean_ctor_get(v_v_1557_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_v_1557_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1580_ = v_v_1557_;
v_isShared_1581_ = v_isSharedCheck_1588_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_node_1578_);
lean_dec(v_v_1557_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1588_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1582_ = lean_usize_shift_right(v_x_1542_, v___x_1547_);
v___x_1583_ = lean_usize_add(v_x_1543_, v___x_1548_);
v___x_1584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_node_1578_, v___x_1582_, v___x_1583_, v_x_1544_, v_x_1545_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1584_);
v___x_1586_ = v___x_1580_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
v___y_1561_ = v___x_1586_;
goto v___jp_1560_;
}
}
}
default: 
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_x_1544_);
lean_ctor_set(v___x_1589_, 1, v_x_1545_);
v___y_1561_ = v___x_1589_;
goto v___jp_1560_;
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_array_fset(v_xs_x27_1559_, v_j_1551_, v___y_1561_);
lean_dec(v_j_1551_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1562_);
v___x_1564_ = v___x_1555_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v_ks_1592_; lean_object* v_vs_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1613_; 
v_ks_1592_ = lean_ctor_get(v_x_1541_, 0);
v_vs_1593_ = lean_ctor_get(v_x_1541_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1541_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1595_ = v_x_1541_;
v_isShared_1596_ = v_isSharedCheck_1613_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_vs_1593_);
lean_inc(v_ks_1592_);
lean_dec(v_x_1541_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1613_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_ks_1592_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_vs_1593_);
v___x_1598_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v_newNode_1599_; uint8_t v___y_1601_; size_t v___x_1607_; uint8_t v___x_1608_; 
v_newNode_1599_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v___x_1598_, v_x_1544_, v_x_1545_);
v___x_1607_ = ((size_t)7ULL);
v___x_1608_ = lean_usize_dec_le(v___x_1607_, v_x_1543_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1599_);
v___x_1610_ = lean_unsigned_to_nat(4u);
v___x_1611_ = lean_nat_dec_lt(v___x_1609_, v___x_1610_);
lean_dec(v___x_1609_);
v___y_1601_ = v___x_1611_;
goto v___jp_1600_;
}
else
{
v___y_1601_ = v___x_1608_;
goto v___jp_1600_;
}
v___jp_1600_:
{
if (v___y_1601_ == 0)
{
lean_object* v_ks_1602_; lean_object* v_vs_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_ks_1602_ = lean_ctor_get(v_newNode_1599_, 0);
lean_inc_ref(v_ks_1602_);
v_vs_1603_ = lean_ctor_get(v_newNode_1599_, 1);
lean_inc_ref(v_vs_1603_);
lean_dec_ref(v_newNode_1599_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_1606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1543_, v_ks_1602_, v_vs_1603_, v___x_1604_, v___x_1605_);
lean_dec_ref(v_vs_1603_);
lean_dec_ref(v_ks_1602_);
return v___x_1606_;
}
else
{
return v_newNode_1599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_1614_, lean_object* v_keys_1615_, lean_object* v_vals_1616_, lean_object* v_i_1617_, lean_object* v_entries_1618_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = lean_array_get_size(v_keys_1615_);
v___x_1620_ = lean_nat_dec_lt(v_i_1617_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_dec(v_i_1617_);
return v_entries_1618_;
}
else
{
lean_object* v_k_1621_; lean_object* v_v_1622_; uint64_t v___x_1623_; size_t v_h_1624_; size_t v___x_1625_; lean_object* v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v_h_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_k_1621_ = lean_array_fget_borrowed(v_keys_1615_, v_i_1617_);
v_v_1622_ = lean_array_fget_borrowed(v_vals_1616_, v_i_1617_);
v___x_1623_ = l_Lean_instHashableMVarId_hash(v_k_1621_);
v_h_1624_ = lean_uint64_to_usize(v___x_1623_);
v___x_1625_ = ((size_t)5ULL);
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_sub(v_depth_1614_, v___x_1627_);
v___x_1629_ = lean_usize_mul(v___x_1625_, v___x_1628_);
v_h_1630_ = lean_usize_shift_right(v_h_1624_, v___x_1629_);
v___x_1631_ = lean_nat_add(v_i_1617_, v___x_1626_);
lean_dec(v_i_1617_);
lean_inc(v_v_1622_);
lean_inc(v_k_1621_);
v___x_1632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_entries_1618_, v_h_1630_, v_depth_1614_, v_k_1621_, v_v_1622_);
v_i_1617_ = v___x_1631_;
v_entries_1618_ = v___x_1632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_1634_, lean_object* v_keys_1635_, lean_object* v_vals_1636_, lean_object* v_i_1637_, lean_object* v_entries_1638_){
_start:
{
size_t v_depth_boxed_1639_; lean_object* v_res_1640_; 
v_depth_boxed_1639_ = lean_unbox_usize(v_depth_1634_);
lean_dec(v_depth_1634_);
v_res_1640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_1639_, v_keys_1635_, v_vals_1636_, v_i_1637_, v_entries_1638_);
lean_dec_ref(v_vals_1636_);
lean_dec_ref(v_keys_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
size_t v_x_1574__boxed_1646_; size_t v_x_1575__boxed_1647_; lean_object* v_res_1648_; 
v_x_1574__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_x_1575__boxed_1647_ = lean_unbox_usize(v_x_1643_);
lean_dec(v_x_1643_);
v_res_1648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1641_, v_x_1574__boxed_1646_, v_x_1575__boxed_1647_, v_x_1644_, v_x_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
uint64_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = l_Lean_instHashableMVarId_hash(v_x_1650_);
v___x_1653_ = lean_uint64_to_usize(v___x_1652_);
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1649_, v___x_1653_, v___x_1654_, v_x_1650_, v_x_1651_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(lean_object* v_mvarId_1656_, lean_object* v_val_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v_mctx_1661_; lean_object* v_cache_1662_; lean_object* v_zetaDeltaFVarIds_1663_; lean_object* v_postponed_1664_; lean_object* v_diag_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1693_; 
v___x_1660_ = lean_st_ref_take(v___y_1658_);
v_mctx_1661_ = lean_ctor_get(v___x_1660_, 0);
v_cache_1662_ = lean_ctor_get(v___x_1660_, 1);
v_zetaDeltaFVarIds_1663_ = lean_ctor_get(v___x_1660_, 2);
v_postponed_1664_ = lean_ctor_get(v___x_1660_, 3);
v_diag_1665_ = lean_ctor_get(v___x_1660_, 4);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1667_ = v___x_1660_;
v_isShared_1668_ = v_isSharedCheck_1693_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_diag_1665_);
lean_inc(v_postponed_1664_);
lean_inc(v_zetaDeltaFVarIds_1663_);
lean_inc(v_cache_1662_);
lean_inc(v_mctx_1661_);
lean_dec(v___x_1660_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1693_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_depth_1669_; lean_object* v_levelAssignDepth_1670_; lean_object* v_lmvarCounter_1671_; lean_object* v_mvarCounter_1672_; lean_object* v_lDecls_1673_; lean_object* v_decls_1674_; lean_object* v_userNames_1675_; lean_object* v_lAssignment_1676_; lean_object* v_eAssignment_1677_; lean_object* v_dAssignment_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1692_; 
v_depth_1669_ = lean_ctor_get(v_mctx_1661_, 0);
v_levelAssignDepth_1670_ = lean_ctor_get(v_mctx_1661_, 1);
v_lmvarCounter_1671_ = lean_ctor_get(v_mctx_1661_, 2);
v_mvarCounter_1672_ = lean_ctor_get(v_mctx_1661_, 3);
v_lDecls_1673_ = lean_ctor_get(v_mctx_1661_, 4);
v_decls_1674_ = lean_ctor_get(v_mctx_1661_, 5);
v_userNames_1675_ = lean_ctor_get(v_mctx_1661_, 6);
v_lAssignment_1676_ = lean_ctor_get(v_mctx_1661_, 7);
v_eAssignment_1677_ = lean_ctor_get(v_mctx_1661_, 8);
v_dAssignment_1678_ = lean_ctor_get(v_mctx_1661_, 9);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_mctx_1661_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1680_ = v_mctx_1661_;
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_dAssignment_1678_);
lean_inc(v_eAssignment_1677_);
lean_inc(v_lAssignment_1676_);
lean_inc(v_userNames_1675_);
lean_inc(v_decls_1674_);
lean_inc(v_lDecls_1673_);
lean_inc(v_mvarCounter_1672_);
lean_inc(v_lmvarCounter_1671_);
lean_inc(v_levelAssignDepth_1670_);
lean_inc(v_depth_1669_);
lean_dec(v_mctx_1661_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_eAssignment_1677_, v_mvarId_1656_, v_val_1657_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 8, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_depth_1669_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_levelAssignDepth_1670_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_lmvarCounter_1671_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_mvarCounter_1672_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_lDecls_1673_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v_decls_1674_);
lean_ctor_set(v_reuseFailAlloc_1691_, 6, v_userNames_1675_);
lean_ctor_set(v_reuseFailAlloc_1691_, 7, v_lAssignment_1676_);
lean_ctor_set(v_reuseFailAlloc_1691_, 8, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 9, v_dAssignment_1678_);
v___x_1684_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1684_);
v___x_1686_ = v___x_1667_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_cache_1662_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_zetaDeltaFVarIds_1663_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_postponed_1664_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_diag_1665_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_st_ref_set(v___y_1658_, v___x_1686_);
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg___boxed(lean_object* v_mvarId_1694_, lean_object* v_val_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1694_, v_val_1695_, v___y_1696_);
lean_dec(v___y_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(lean_object* v_a_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = l_Lean_Expr_mvarId_x21(v_x_1700_);
v___x_1702_ = l_Lean_instBEqMVarId_beq(v___x_1701_, v_a_1699_);
lean_dec(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed(lean_object* v_a_1703_, lean_object* v_x_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(v_a_1703_, v_x_1704_);
lean_dec_ref(v_x_1704_);
lean_dec(v_a_1703_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_argMVars_1707_, lean_object* v_argVars_1708_, lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1712_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v_a_1721_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1720_ = lean_box(0);
v_a_1721_ = lean_array_uget_borrowed(v_as_1709_, v_i_1711_);
lean_inc(v_a_1721_);
v___f_1742_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1742_, 0, v_a_1721_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = l_Array_findIdx_x3f_loop___redArg(v___f_1742_, v_argMVars_1707_, v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 1)
{
lean_object* v_val_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1745_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = l_Lean_instInhabitedExpr;
v___x_1747_ = lean_array_get_borrowed(v___x_1746_, v_argVars_1708_, v_val_1745_);
lean_dec(v_val_1745_);
lean_inc(v___x_1747_);
lean_inc(v_a_1721_);
v___x_1748_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_a_1721_, v___x_1747_, v___y_1714_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref(v___x_1748_);
v___y_1723_ = v___y_1713_;
v___y_1724_ = v___y_1714_;
v___y_1725_ = v___y_1715_;
v___y_1726_ = v___y_1716_;
goto v___jp_1722_;
}
else
{
return v___x_1748_;
}
}
else
{
lean_dec(v___x_1744_);
v___y_1723_ = v___y_1713_;
v___y_1724_ = v___y_1714_;
v___y_1725_ = v___y_1715_;
v___y_1726_ = v___y_1716_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_inc(v_a_1721_);
v___x_1727_ = l_Lean_Expr_mvar___override(v_a_1721_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
v___x_1728_ = lean_infer_type(v___x_1727_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1707_, v_argVars_1708_, v_a_1729_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1730_) == 0)
{
size_t v___x_1731_; size_t v___x_1732_; 
lean_dec_ref(v___x_1730_);
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1711_, v___x_1731_);
v_i_1711_ = v___x_1732_;
v_b_1712_ = v___x_1720_;
goto _start;
}
else
{
return v___x_1730_;
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1734_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1728_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1728_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1749_, lean_object* v_argVars_1750_, lean_object* v_e_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_getMVars(v_e_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = lean_box(0);
v_sz_1760_ = lean_array_size(v_a_1758_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1749_, v_argVars_1750_, v_a_1758_, v_sz_1760_, v___x_1761_, v___x_1759_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1758_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1762_, 0);
lean_dec(v_unused_1770_);
v___x_1764_ = v___x_1762_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v___x_1762_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1759_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1759_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
return v___x_1762_;
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1757_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1757_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1779_, lean_object* v_argVars_1780_, lean_object* v_e_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1779_, v_argVars_1780_, v_e_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec_ref(v_argVars_1780_);
lean_dec_ref(v_argMVars_1779_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_argMVars_1788_, lean_object* v_argVars_1789_, lean_object* v_as_1790_, lean_object* v_sz_1791_, lean_object* v_i_1792_, lean_object* v_b_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
size_t v_sz_boxed_1799_; size_t v_i_boxed_1800_; lean_object* v_res_1801_; 
v_sz_boxed_1799_ = lean_unbox_usize(v_sz_1791_);
lean_dec(v_sz_1791_);
v_i_boxed_1800_ = lean_unbox_usize(v_i_1792_);
lean_dec(v_i_1792_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1788_, v_argVars_1789_, v_as_1790_, v_sz_boxed_1799_, v_i_boxed_1800_, v_b_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v_as_1790_);
lean_dec_ref(v_argVars_1789_);
lean_dec_ref(v_argMVars_1788_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_mvarId_1802_, lean_object* v_val_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1802_, v_val_1803_, v___y_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_mvarId_1810_, lean_object* v_val_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_mvarId_1810_, v_val_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_x_1819_, v_x_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1823_, lean_object* v_x_1824_, size_t v_x_1825_, size_t v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1824_, v_x_1825_, v_x_1826_, v_x_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
size_t v_x_1946__boxed_1836_; size_t v_x_1947__boxed_1837_; lean_object* v_res_1838_; 
v_x_1946__boxed_1836_ = lean_unbox_usize(v_x_1832_);
lean_dec(v_x_1832_);
v_x_1947__boxed_1837_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_res_1838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(v_00_u03b2_1830_, v_x_1831_, v_x_1946__boxed_1836_, v_x_1947__boxed_1837_, v_x_1834_, v_x_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1839_, lean_object* v_n_1840_, lean_object* v_k_1841_, lean_object* v_v_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1840_, v_k_1841_, v_v_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1844_, size_t v_depth_1845_, lean_object* v_keys_1846_, lean_object* v_vals_1847_, lean_object* v_heq_1848_, lean_object* v_i_1849_, lean_object* v_entries_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1845_, v_keys_1846_, v_vals_1847_, v_i_1849_, v_entries_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_depth_1853_, lean_object* v_keys_1854_, lean_object* v_vals_1855_, lean_object* v_heq_1856_, lean_object* v_i_1857_, lean_object* v_entries_1858_){
_start:
{
size_t v_depth_boxed_1859_; lean_object* v_res_1860_; 
v_depth_boxed_1859_ = lean_unbox_usize(v_depth_1853_);
lean_dec(v_depth_1853_);
v_res_1860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1852_, v_depth_boxed_1859_, v_keys_1854_, v_vals_1855_, v_heq_1856_, v_i_1857_, v_entries_1858_);
lean_dec_ref(v_vals_1855_);
lean_dec_ref(v_keys_1854_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_1862_, v_x_1863_, v_x_1864_, v_x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1867_, lean_object* v___y_1868_){
_start:
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_Expr_hasMVar(v_e_1867_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_e_1867_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v_mctx_1873_; lean_object* v___x_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___x_1877_; lean_object* v_cache_1878_; lean_object* v_zetaDeltaFVarIds_1879_; lean_object* v_postponed_1880_; lean_object* v_diag_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1890_; 
v___x_1872_ = lean_st_ref_get(v___y_1868_);
v_mctx_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_mctx_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = l_Lean_instantiateMVarsCore(v_mctx_1873_, v_e_1867_);
v_fst_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec_ref(v___x_1874_);
v___x_1877_ = lean_st_ref_take(v___y_1868_);
v_cache_1878_ = lean_ctor_get(v___x_1877_, 1);
v_zetaDeltaFVarIds_1879_ = lean_ctor_get(v___x_1877_, 2);
v_postponed_1880_ = lean_ctor_get(v___x_1877_, 3);
v_diag_1881_ = lean_ctor_get(v___x_1877_, 4);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1891_);
v___x_1883_ = v___x_1877_;
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_diag_1881_);
lean_inc(v_postponed_1880_);
lean_inc(v_zetaDeltaFVarIds_1879_);
lean_inc(v_cache_1878_);
lean_dec(v___x_1877_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v_snd_1876_);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_snd_1876_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_cache_1878_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_zetaDeltaFVarIds_1879_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_postponed_1880_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_diag_1881_);
v___x_1886_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_st_ref_set(v___y_1868_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_fst_1875_);
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1892_, v___y_1893_);
lean_dec(v___y_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1896_, v___y_1898_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1910_, lean_object* v_opt_1911_){
_start:
{
lean_object* v_name_1912_; lean_object* v_defValue_1913_; lean_object* v_map_1914_; lean_object* v___x_1915_; 
v_name_1912_ = lean_ctor_get(v_opt_1911_, 0);
v_defValue_1913_ = lean_ctor_get(v_opt_1911_, 1);
v_map_1914_ = lean_ctor_get(v_opts_1910_, 0);
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1914_, v_name_1912_);
if (lean_obj_tag(v___x_1915_) == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_unbox(v_defValue_1913_);
return v___x_1916_;
}
else
{
lean_object* v_val_1917_; 
v_val_1917_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_val_1917_);
lean_dec_ref(v___x_1915_);
if (lean_obj_tag(v_val_1917_) == 1)
{
uint8_t v_v_1918_; 
v_v_1918_ = lean_ctor_get_uint8(v_val_1917_, 0);
lean_dec_ref(v_val_1917_);
return v_v_1918_;
}
else
{
uint8_t v___x_1919_; 
lean_dec(v_val_1917_);
v___x_1919_ = lean_unbox(v_defValue_1913_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1920_, lean_object* v_opt_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1920_, v_opt_1921_);
lean_dec_ref(v_opt_1921_);
lean_dec_ref(v_opts_1920_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1924_, lean_object* v_as_1925_, size_t v_i_1926_, size_t v_stop_1927_){
_start:
{
uint8_t v___x_1928_; 
v___x_1928_ = lean_usize_dec_eq(v_i_1926_, v_stop_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = lean_array_uget_borrowed(v_as_1925_, v_i_1926_);
v___x_1930_ = lean_nat_dec_eq(v_a_1924_, v___x_1929_);
if (v___x_1930_ == 0)
{
size_t v___x_1931_; size_t v___x_1932_; 
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_i_1926_, v___x_1931_);
v_i_1926_ = v___x_1932_;
goto _start;
}
else
{
return v___x_1930_;
}
}
else
{
uint8_t v___x_1934_; 
v___x_1934_ = 0;
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1935_, lean_object* v_as_1936_, lean_object* v_i_1937_, lean_object* v_stop_1938_){
_start:
{
size_t v_i_boxed_1939_; size_t v_stop_boxed_1940_; uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_i_boxed_1939_ = lean_unbox_usize(v_i_1937_);
lean_dec(v_i_1937_);
v_stop_boxed_1940_ = lean_unbox_usize(v_stop_1938_);
lean_dec(v_stop_1938_);
v_res_1941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1935_, v_as_1936_, v_i_boxed_1939_, v_stop_boxed_1940_);
lean_dec_ref(v_as_1936_);
lean_dec(v_a_1935_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_array_get_size(v_as_1943_);
v___x_1947_ = lean_nat_dec_lt(v___x_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
return v___x_1947_;
}
else
{
if (v___x_1947_ == 0)
{
return v___x_1947_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1946_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1944_, v_as_1943_, v___x_1948_, v___x_1949_);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1951_, lean_object* v_a_1952_){
_start:
{
uint8_t v_res_1953_; lean_object* v_r_1954_; 
v_res_1953_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_as_1951_);
v_r_1954_ = lean_box(v_res_1953_);
return v_r_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1955_, lean_object* v_fst_1956_, lean_object* v_argVars_1957_, lean_object* v_as_1958_, size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_a_1968_; uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_b_1961_);
return v___x_1973_;
}
else
{
lean_object* v_next_1974_; 
v_next_1974_ = lean_ctor_get(v_b_1961_, 0);
lean_inc(v_next_1974_);
if (lean_obj_tag(v_next_1974_) == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_b_1961_);
return v___x_1975_;
}
else
{
lean_object* v_upperBound_1976_; lean_object* v_val_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2008_; 
v_upperBound_1976_ = lean_ctor_get(v_b_1961_, 1);
v_val_1977_ = lean_ctor_get(v_next_1974_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_next_1974_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1979_ = v_next_1974_;
v_isShared_1980_ = v_isSharedCheck_2008_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_val_1977_);
lean_dec(v_next_1974_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2008_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_nat_dec_lt(v_val_1977_, v_upperBound_1976_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_del_object(v___x_1979_);
lean_dec(v_val_1977_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_b_1961_);
return v___x_1982_;
}
else
{
lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2005_; 
lean_inc(v_upperBound_1976_);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_b_1961_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; lean_object* v_unused_2007_; 
v_unused_2006_ = lean_ctor_get(v_b_1961_, 1);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_b_1961_, 0);
lean_dec(v_unused_2007_);
v___x_1984_ = v_b_1961_;
v_isShared_1985_ = v_isSharedCheck_2005_;
goto v_resetjp_1983_;
}
else
{
lean_dec(v_b_1961_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2005_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_val_1977_, v___x_1986_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1987_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1989_);
v___x_1991_ = v___x_1984_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_upperBound_1976_);
v___x_1991_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1955_, v_val_1977_);
lean_dec(v_val_1977_);
if (v___x_1992_ == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; 
v_a_1993_ = lean_array_uget_borrowed(v_as_1958_, v_i_1960_);
lean_inc(v_a_1993_);
v___x_1994_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1956_, v_argVars_1957_, v_a_1993_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_dec_ref(v___x_1994_);
v_a_1968_ = v___x_1991_;
goto v___jp_1967_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v___x_1991_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
v_a_1968_ = v___x_1991_;
goto v___jp_1967_;
}
}
}
}
}
}
}
}
v___jp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1960_, v___x_1969_);
v_i_1960_ = v___x_1970_;
v_b_1961_ = v_a_1968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2009_, lean_object* v_fst_2010_, lean_object* v_argVars_2011_, lean_object* v_as_2012_, lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
size_t v_sz_boxed_2021_; size_t v_i_boxed_2022_; lean_object* v_res_2023_; 
v_sz_boxed_2021_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2022_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2009_, v_fst_2010_, v_argVars_2011_, v_as_2012_, v_sz_boxed_2021_, v_i_boxed_2022_, v_b_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_as_2012_);
lean_dec_ref(v_argVars_2011_);
lean_dec_ref(v_fst_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
if (lean_obj_tag(v_a_2025_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = l_List_reverse___redArg(v_a_2026_);
return v___x_2027_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2044_; 
v_head_2028_ = lean_ctor_get(v_a_2025_, 0);
v_tail_2029_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2031_ = v_a_2025_;
v_isShared_2032_ = v_isSharedCheck_2044_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_tail_2029_);
lean_inc(v_head_2028_);
lean_dec(v_a_2025_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2044_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2033_ = 0;
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_array_get(v___x_2034_, v_fst_2024_, v_head_2028_);
lean_dec(v___x_2034_);
v___x_2036_ = 3;
v___x_2037_ = lean_unbox(v___x_2035_);
lean_dec(v___x_2035_);
v___x_2038_ = l_Lean_instBEqBinderInfo_beq(v___x_2037_, v___x_2036_);
if (v___x_2038_ == 0)
{
lean_del_object(v___x_2031_);
lean_dec(v_head_2028_);
v_a_2025_ = v_tail_2029_;
goto _start;
}
else
{
lean_object* v___x_2041_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_a_2026_);
v___x_2041_ = v___x_2031_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_head_2028_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2026_);
v___x_2041_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
v_a_2025_ = v_tail_2029_;
v_a_2026_ = v___x_2041_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2045_, v_a_2046_, v_a_2047_);
lean_dec_ref(v_fst_2045_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2049_, lean_object* v___x_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_b_2053_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_nat_dec_lt(v_a_2052_, v_upperBound_2049_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v_a_2052_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_b_2053_);
return v___x_2056_;
}
else
{
lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2098_; 
v_snd_2057_ = lean_ctor_get(v_b_2053_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_b_2053_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_b_2053_, 0);
lean_dec(v_unused_2099_);
v___x_2059_ = v_b_2053_;
v_isShared_2060_ = v_isSharedCheck_2098_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_dec(v_b_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2098_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_array_2061_; lean_object* v_start_2062_; lean_object* v_stop_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_array_2061_ = lean_ctor_get(v_snd_2057_, 0);
v_start_2062_ = lean_ctor_get(v_snd_2057_, 1);
v_stop_2063_ = lean_ctor_get(v_snd_2057_, 2);
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_nat_dec_lt(v_start_2062_, v_stop_2063_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v_a_2052_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2064_);
v___x_2067_ = v___x_2059_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_snd_2057_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
else
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2094_; 
lean_inc(v_stop_2063_);
lean_inc(v_start_2062_);
lean_inc_ref(v_array_2061_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_snd_2057_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2095_ = lean_ctor_get(v_snd_2057_, 2);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_snd_2057_, 1);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_snd_2057_, 0);
lean_dec(v_unused_2097_);
v___x_2071_ = v_snd_2057_;
v_isShared_2072_ = v_isSharedCheck_2094_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_snd_2057_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2094_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_nat_dec_eq(v___x_2050_, v___x_2073_);
v___x_2075_ = lean_array_fget(v_array_2061_, v_start_2062_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_add(v_start_2062_, v___x_2076_);
lean_dec(v_start_2062_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2077_);
v___x_2079_ = v___x_2071_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_array_2061_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_stop_2063_);
v___x_2079_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
uint8_t v___x_2092_; 
v___x_2092_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2051_, v_a_2052_);
if (v___x_2092_ == 0)
{
goto v___jp_2086_;
}
else
{
if (v___x_2074_ == 0)
{
lean_dec(v___x_2075_);
goto v___jp_2080_;
}
else
{
goto v___jp_2086_;
}
}
v___jp_2080_:
{
lean_object* v___x_2082_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2079_);
lean_ctor_set(v___x_2059_, 0, v___x_2064_);
v___x_2082_ = v___x_2059_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2079_);
v___x_2082_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_nat_add(v_a_2052_, v___x_2076_);
lean_dec(v_a_2052_);
v_a_2052_ = v___x_2083_;
v_b_2053_ = v___x_2082_;
goto _start;
}
}
v___jp_2086_:
{
uint8_t v___x_2087_; 
v___x_2087_ = l_Lean_Expr_hasExprMVar(v___x_2075_);
lean_dec(v___x_2075_);
if (v___x_2087_ == 0)
{
goto v___jp_2080_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2059_);
lean_dec(v_a_2052_);
v___x_2088_ = lean_box(v___x_2074_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2079_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2100_, lean_object* v___x_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2100_, v___x_2101_, v_a_2102_, v_a_2103_, v_b_2104_);
lean_dec_ref(v_a_2102_);
lean_dec(v___x_2101_);
lean_dec(v_upperBound_2100_);
return v_res_2106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2107_; lean_object* v_dummy_2108_; 
v___x_2107_ = lean_box(0);
v_dummy_2108_ = l_Lean_Expr_sort___override(v___x_2107_);
return v_dummy_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2109_, lean_object* v___x_2110_, uint8_t v___x_2111_, lean_object* v_x_2112_, lean_object* v_argTy_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
v___x_2119_ = lean_whnf(v_argTy_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2120_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_dummy_2123_; lean_object* v_nargs_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
v_dummy_2123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2124_ = l_Lean_Expr_getAppNumArgs(v_a_2120_);
lean_inc(v_nargs_2124_);
v___x_2125_ = lean_mk_array(v_nargs_2124_, v_dummy_2123_);
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_sub(v_nargs_2124_, v___x_2126_);
lean_dec(v_nargs_2124_);
v___x_2128_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2120_, v___x_2125_, v___x_2127_);
v___x_2129_ = lean_array_get_size(v___x_2128_);
lean_inc(v___x_2109_);
v___x_2130_ = l_Array_toSubarray___redArg(v___x_2128_, v___x_2109_, v___x_2129_);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
v___x_2133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2129_, v___x_2110_, v_a_2122_, v___x_2109_, v___x_2132_);
lean_dec(v_a_2122_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2147_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; 
v_fst_2138_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_fst_2138_);
lean_dec(v_a_2134_);
if (lean_obj_tag(v_fst_2138_) == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_box(v___x_2111_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; 
v_val_2143_ = lean_ctor_get(v_fst_2138_, 0);
lean_inc(v_val_2143_);
lean_dec_ref(v_fst_2138_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_val_2143_);
v___x_2145_ = v___x_2136_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_val_2143_);
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
v_a_2148_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2133_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2133_);
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
lean_dec(v_a_2120_);
lean_dec(v___x_2109_);
v_a_2156_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2121_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2121_);
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
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v___x_2109_);
v_a_2164_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2119_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2119_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v_x_2175_, lean_object* v_argTy_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v___x_24484__boxed_2182_; lean_object* v_res_2183_; 
v___x_24484__boxed_2182_ = lean_unbox(v___x_2174_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2172_, v___x_2173_, v___x_24484__boxed_2182_, v_x_2175_, v_argTy_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec_ref(v_x_2175_);
lean_dec(v___x_2173_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2187_, lean_object* v_projInfo_x3f_2188_, lean_object* v___x_2189_, lean_object* v_argVars_2190_, lean_object* v_as_2191_, size_t v_sz_2192_, size_t v_i_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v___x_2200_; 
v___x_2200_ = lean_usize_dec_lt(v_i_2193_, v_sz_2192_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v___x_2189_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_b_2194_);
return v___x_2201_;
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref(v_b_2194_);
v_a_2202_ = lean_array_uget_borrowed(v_as_2191_, v_i_2193_);
v___x_2203_ = l_Lean_instInhabitedExpr;
v___x_2204_ = lean_array_get_borrowed(v___x_2203_, v_fst_2187_, v_a_2202_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___x_2204_);
v___x_2205_ = lean_infer_type(v___x_2204_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2206_, v___y_2196_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2254_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2254_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2254_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2220_; lean_object* v___y_2222_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; uint8_t v___x_2239_; 
v___x_2212_ = lean_box(0);
v___x_2220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = lean_box(v___x_2200_);
lean_inc(v___x_2189_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2238_, 0, v___x_2236_);
lean_closure_set(v___f_2238_, 1, v___x_2189_);
lean_closure_set(v___f_2238_, 2, v___x_2237_);
v___x_2239_ = lean_nat_dec_eq(v___x_2189_, v___x_2236_);
if (lean_obj_tag(v_projInfo_x3f_2188_) == 1)
{
lean_object* v_val_2240_; lean_object* v_numParams_2241_; uint8_t v___x_2242_; 
v_val_2240_ = lean_ctor_get(v_projInfo_x3f_2188_, 0);
v_numParams_2241_ = lean_ctor_get(v_val_2240_, 1);
v___x_2242_ = lean_nat_dec_eq(v_numParams_2241_, v_a_2202_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2208_, v___f_2238_, v___x_2239_, v___x_2239_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
v___y_2222_ = v___x_2243_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2244_; 
lean_dec_ref(v___f_2238_);
lean_dec(v___x_2189_);
v___x_2244_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2187_, v_argVars_2190_, v_a_2208_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_dec_ref(v___x_2244_);
goto v___jp_2213_;
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_del_object(v___x_2210_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2208_, v___f_2238_, v___x_2239_, v___x_2239_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
v___y_2222_ = v___x_2253_;
goto v___jp_2221_;
}
v___jp_2213_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_inc(v_a_2202_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2202_);
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2212_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2216_);
v___x_2218_ = v___x_2210_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
v___jp_2221_:
{
if (lean_obj_tag(v___y_2222_) == 0)
{
lean_object* v_a_2223_; uint8_t v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___y_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___y_2222_);
v___x_2224_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
if (v___x_2224_ == 0)
{
size_t v___x_2225_; size_t v___x_2226_; 
lean_del_object(v___x_2210_);
v___x_2225_ = ((size_t)1ULL);
v___x_2226_ = lean_usize_add(v_i_2193_, v___x_2225_);
v_i_2193_ = v___x_2226_;
v_b_2194_ = v___x_2220_;
goto _start;
}
else
{
lean_dec(v___x_2189_);
goto v___jp_2213_;
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_del_object(v___x_2210_);
lean_dec(v___x_2189_);
v_a_2228_ = lean_ctor_get(v___y_2222_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___y_2222_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___y_2222_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___y_2222_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2189_);
v_a_2255_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2207_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2207_);
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
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v___x_2189_);
v_a_2263_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2205_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2205_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2271_, lean_object* v_projInfo_x3f_2272_, lean_object* v___x_2273_, lean_object* v_argVars_2274_, lean_object* v_as_2275_, lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2271_, v_projInfo_x3f_2272_, v___x_2273_, v_argVars_2274_, v_as_2275_, v_sz_boxed_2284_, v_i_boxed_2285_, v_b_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v_as_2275_);
lean_dec_ref(v_argVars_2274_);
lean_dec(v_projInfo_x3f_2272_);
lean_dec_ref(v_fst_2271_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v_env_2294_; lean_object* v___x_2295_; lean_object* v_mctx_2296_; lean_object* v_lctx_2297_; lean_object* v_options_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2293_ = lean_st_ref_get(v___y_2291_);
v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_ref(v_env_2294_);
lean_dec(v___x_2293_);
v___x_2295_ = lean_st_ref_get(v___y_2289_);
v_mctx_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc_ref(v_mctx_2296_);
lean_dec(v___x_2295_);
v_lctx_2297_ = lean_ctor_get(v___y_2288_, 2);
v_options_2298_ = lean_ctor_get(v___y_2290_, 2);
lean_inc_ref(v_options_2298_);
lean_inc_ref(v_lctx_2297_);
v___x_2299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2299_, 0, v_env_2294_);
lean_ctor_set(v___x_2299_, 1, v_mctx_2296_);
lean_ctor_set(v___x_2299_, 2, v_lctx_2297_);
lean_ctor_set(v___x_2299_, 3, v_options_2298_);
v___x_2300_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_msgData_2287_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_ref_2315_; lean_object* v___x_2316_; lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
v_ref_2315_ = lean_ctor_get(v___y_2312_, 5);
v___x_2316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_inc(v_ref_2315_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_ref_2315_);
lean_ctor_set(v___x_2321_, 1, v_a_2317_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set_tag(v___x_2319_, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2333_, lean_object* v_as_2334_, size_t v_i_2335_, size_t v_stop_2336_, lean_object* v_b_2337_){
_start:
{
lean_object* v___y_2339_; uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_eq(v_i_2335_, v_stop_2336_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_array_uget_borrowed(v_as_2334_, v_i_2335_);
v___x_2345_ = lean_nat_dec_eq(v___x_2344_, v_next_2333_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; 
lean_inc(v___x_2344_);
v___x_2346_ = lean_array_push(v_b_2337_, v___x_2344_);
v___y_2339_ = v___x_2346_;
goto v___jp_2338_;
}
else
{
v___y_2339_ = v_b_2337_;
goto v___jp_2338_;
}
}
else
{
return v_b_2337_;
}
v___jp_2338_:
{
size_t v___x_2340_; size_t v___x_2341_; 
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_add(v_i_2335_, v___x_2340_);
v_i_2335_ = v___x_2341_;
v_b_2337_ = v___y_2339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2347_, lean_object* v_as_2348_, lean_object* v_i_2349_, lean_object* v_stop_2350_, lean_object* v_b_2351_){
_start:
{
size_t v_i_boxed_2352_; size_t v_stop_boxed_2353_; lean_object* v_res_2354_; 
v_i_boxed_2352_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_stop_boxed_2353_ = lean_unbox_usize(v_stop_2350_);
lean_dec(v_stop_2350_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2347_, v_as_2348_, v_i_boxed_2352_, v_stop_boxed_2353_, v_b_2351_);
lean_dec_ref(v_as_2348_);
lean_dec(v_next_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2355_, size_t v_sz_2356_, size_t v_i_2357_, lean_object* v_bs_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_usize_dec_lt(v_i_2357_, v_sz_2356_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_bs_2358_);
return v___x_2365_;
}
else
{
lean_object* v_v_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_v_2366_ = lean_array_uget_borrowed(v_bs_2358_, v_i_2357_);
v___x_2367_ = l_Lean_instInhabitedExpr;
v___x_2368_ = lean_array_get_borrowed(v___x_2367_, v_fst_2355_, v_v_2366_);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v___y_2360_);
lean_inc_ref(v___y_2359_);
lean_inc(v___x_2368_);
v___x_2369_ = lean_infer_type(v___x_2368_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2370_, v___y_2360_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v_bs_x27_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = lean_unsigned_to_nat(0u);
v_bs_x27_2374_ = lean_array_uset(v_bs_2358_, v_i_2357_, v___x_2373_);
v___x_2375_ = l_Lean_Expr_setPPExplicit(v_a_2372_, v___x_2364_);
v___x_2376_ = l_Lean_indentExpr(v___x_2375_);
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_add(v_i_2357_, v___x_2377_);
v___x_2379_ = lean_array_uset(v_bs_x27_2374_, v_i_2357_, v___x_2376_);
v_i_2357_ = v___x_2378_;
v_bs_2358_ = v___x_2379_;
goto _start;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_bs_2358_);
v_a_2381_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2371_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2371_);
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
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_bs_2358_);
v_a_2389_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2369_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2369_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2397_, lean_object* v_sz_2398_, lean_object* v_i_2399_, lean_object* v_bs_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
size_t v_sz_boxed_2406_; size_t v_i_boxed_2407_; lean_object* v_res_2408_; 
v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2398_);
lean_dec(v_sz_2398_);
v_i_boxed_2407_ = lean_unbox_usize(v_i_2399_);
lean_dec(v_i_2399_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2397_, v_sz_boxed_2406_, v_i_boxed_2407_, v_bs_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v_fst_2397_);
return v_res_2408_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2413_ = l_Lean_MessageData_ofFormat(v___x_2412_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2416_ = l_Lean_stringToMessageData(v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2423_, lean_object* v_argVars_2424_, lean_object* v_inst_2425_, lean_object* v_a_2426_, lean_object* v_projInfo_x3f_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2565_; 
v_fst_2474_ = lean_ctor_get(v_b_2428_, 0);
v_snd_2475_ = lean_ctor_get(v_b_2428_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_b_2428_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2477_ = v_b_2428_;
v_isShared_2478_ = v_isSharedCheck_2565_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_snd_2475_);
lean_inc(v_fst_2474_);
lean_dec(v_b_2428_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2565_;
goto v_resetjp_2476_;
}
v___jp_2434_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = l_Lean_instInhabitedExpr;
v___x_2443_ = lean_array_get_borrowed(v___x_2442_, v_fst_2423_, v___y_2437_);
lean_dec(v___y_2437_);
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2436_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2440_);
lean_inc(v___x_2443_);
v___x_2444_ = lean_infer_type(v___x_2443_, v___y_2440_, v___y_2438_, v___y_2436_, v___y_2439_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v___x_2444_);
v___x_2446_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2423_, v_argVars_2424_, v_a_2445_, v___y_2440_, v___y_2438_, v___y_2436_, v___y_2439_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref(v___x_2446_);
lean_inc(v___x_2443_);
v___x_2447_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2423_, v_argVars_2424_, v___x_2443_, v___y_2440_, v___y_2438_, v___y_2436_, v___y_2439_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v___x_2447_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2435_);
lean_ctor_set(v___x_2448_, 1, v___y_2441_);
v_b_2428_ = v___x_2448_;
goto _start;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2450_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2447_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2447_);
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
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2458_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2446_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2446_);
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
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2466_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2444_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2444_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
v_resetjp_2476_:
{
lean_object* v_next_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_array_get_size(v_snd_2475_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_nat_dec_eq(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
lean_del_object(v___x_2477_);
v___x_2545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2546_ = lean_array_size(v_snd_2475_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2423_, v_projInfo_x3f_2427_, v___x_2542_, v_argVars_2424_, v_snd_2475_, v_sz_2546_, v___x_2547_, v___x_2545_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_fst_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v_fst_2550_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_fst_2550_);
lean_dec(v_a_2549_);
if (lean_obj_tag(v_fst_2550_) == 0)
{
goto v___jp_2504_;
}
else
{
lean_object* v_val_2551_; 
v_val_2551_ = lean_ctor_get(v_fst_2550_, 0);
lean_inc(v_val_2551_);
lean_dec_ref(v_fst_2550_);
if (lean_obj_tag(v_val_2551_) == 0)
{
goto v___jp_2504_;
}
else
{
lean_object* v_val_2552_; 
v_val_2552_ = lean_ctor_get(v_val_2551_, 0);
lean_inc(v_val_2552_);
lean_dec_ref(v_val_2551_);
v_next_2480_ = v_val_2552_;
v___y_2481_ = v___y_2429_;
v___y_2482_ = v___y_2430_;
v___y_2483_ = v___y_2431_;
v___y_2484_ = v___y_2432_;
goto v___jp_2479_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_snd_2475_);
lean_dec(v_fst_2474_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2553_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2548_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v___x_2562_; 
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
if (v_isShared_2478_ == 0)
{
v___x_2562_ = v___x_2477_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_fst_2474_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_snd_2475_);
v___x_2562_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
}
v___jp_2479_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
lean_inc(v_next_2480_);
v___x_2485_ = lean_array_push(v_fst_2474_, v_next_2480_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_array_get_size(v_snd_2475_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2489_ = lean_nat_dec_lt(v___x_2486_, v___x_2487_);
if (v___x_2489_ == 0)
{
lean_dec(v_snd_2475_);
v___y_2435_ = v___x_2485_;
v___y_2436_ = v___y_2483_;
v___y_2437_ = v_next_2480_;
v___y_2438_ = v___y_2482_;
v___y_2439_ = v___y_2484_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2488_;
goto v___jp_2434_;
}
else
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_le(v___x_2487_, v___x_2487_);
if (v___x_2490_ == 0)
{
if (v___x_2489_ == 0)
{
lean_dec(v_snd_2475_);
v___y_2435_ = v___x_2485_;
v___y_2436_ = v___y_2483_;
v___y_2437_ = v_next_2480_;
v___y_2438_ = v___y_2482_;
v___y_2439_ = v___y_2484_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2488_;
goto v___jp_2434_;
}
else
{
size_t v___x_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = lean_usize_of_nat(v___x_2487_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2480_, v_snd_2475_, v___x_2491_, v___x_2492_, v___x_2488_);
lean_dec(v_snd_2475_);
v___y_2435_ = v___x_2485_;
v___y_2436_ = v___y_2483_;
v___y_2437_ = v_next_2480_;
v___y_2438_ = v___y_2482_;
v___y_2439_ = v___y_2484_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2493_;
goto v___jp_2434_;
}
}
else
{
size_t v___x_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = lean_usize_of_nat(v___x_2487_);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2480_, v_snd_2475_, v___x_2494_, v___x_2495_, v___x_2488_);
lean_dec(v_snd_2475_);
v___y_2435_ = v___x_2485_;
v___y_2436_ = v___y_2483_;
v___y_2437_ = v_next_2480_;
v___y_2438_ = v___y_2482_;
v___y_2439_ = v___y_2484_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2496_;
goto v___jp_2434_;
}
}
}
v___jp_2497_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_array_get_borrowed(v___x_2502_, v_snd_2475_, v___x_2502_);
lean_inc(v___x_2503_);
v_next_2480_ = v___x_2503_;
v___y_2481_ = v___y_2498_;
v___y_2482_ = v___y_2499_;
v___y_2483_ = v___y_2500_;
v___y_2484_ = v___y_2501_;
goto v___jp_2479_;
}
v___jp_2504_:
{
lean_object* v_options_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_options_2505_ = lean_ctor_get(v___y_2431_, 2);
v___x_2506_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2507_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
v___y_2498_ = v___y_2429_;
v___y_2499_ = v___y_2430_;
v___y_2500_ = v___y_2431_;
v___y_2501_ = v___y_2432_;
goto v___jp_2497_;
}
else
{
size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v_sz_2508_ = lean_array_size(v_snd_2475_);
v___x_2509_ = ((size_t)0ULL);
lean_inc(v_snd_2475_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2423_, v_sz_2508_, v___x_2509_, v_snd_2475_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = lean_array_to_list(v_a_2511_);
v___x_2513_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2514_ = l_Lean_MessageData_joinSep(v___x_2512_, v___x_2513_);
v___x_2515_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2425_);
v___x_2516_ = l_Lean_MessageData_ofExpr(v_inst_2425_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
lean_inc_ref(v_a_2426_);
v___x_2520_ = l_Lean_indentExpr(v_a_2426_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2514_);
v___x_2525_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2524_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_dec_ref(v___x_2525_);
v___y_2498_ = v___y_2429_;
v___y_2499_ = v___y_2430_;
v___y_2500_ = v___y_2431_;
v___y_2501_ = v___y_2432_;
goto v___jp_2497_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_snd_2475_);
lean_dec(v_fst_2474_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
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
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_snd_2475_);
lean_dec(v_fst_2474_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_inst_2425_);
v_a_2534_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2510_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2510_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2566_, lean_object* v_argVars_2567_, lean_object* v_inst_2568_, lean_object* v_a_2569_, lean_object* v_projInfo_x3f_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2566_, v_argVars_2567_, v_inst_2568_, v_a_2569_, v_projInfo_x3f_2570_, v_b_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v_projInfo_x3f_2570_);
lean_dec_ref(v_argVars_2567_);
lean_dec_ref(v_fst_2566_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2578_, size_t v_sz_2579_, size_t v_i_2580_, lean_object* v_bs_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_usize_dec_lt(v_i_2580_, v_sz_2579_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_bs_2581_);
return v___x_2588_;
}
else
{
lean_object* v_v_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_v_2589_ = lean_array_uget_borrowed(v_bs_2581_, v_i_2580_);
v___x_2590_ = l_Lean_instInhabitedExpr;
v___x_2591_ = lean_array_get_borrowed(v___x_2590_, v_argVars_2578_, v_v_2589_);
lean_inc(v___y_2585_);
lean_inc_ref(v___y_2584_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc(v___x_2591_);
v___x_2592_ = lean_infer_type(v___x_2591_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v_bs_x27_2595_; lean_object* v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; lean_object* v___x_2599_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v_bs_x27_2595_ = lean_array_uset(v_bs_2581_, v_i_2580_, v___x_2594_);
v___x_2596_ = l_Lean_indentExpr(v_a_2593_);
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2580_, v___x_2597_);
v___x_2599_ = lean_array_uset(v_bs_x27_2595_, v_i_2580_, v___x_2596_);
v_i_2580_ = v___x_2598_;
v_bs_2581_ = v___x_2599_;
goto _start;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_bs_2581_);
v_a_2601_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2592_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2592_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2609_, lean_object* v_sz_2610_, lean_object* v_i_2611_, lean_object* v_bs_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
size_t v_sz_boxed_2618_; size_t v_i_boxed_2619_; lean_object* v_res_2620_; 
v_sz_boxed_2618_ = lean_unbox_usize(v_sz_2610_);
lean_dec(v_sz_2610_);
v_i_boxed_2619_ = lean_unbox_usize(v_i_2611_);
lean_dec(v_i_2611_);
v_res_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2609_, v_sz_boxed_2618_, v_i_boxed_2619_, v_bs_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_argVars_2609_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
if (lean_obj_tag(v_a_2621_) == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = l_List_reverse___redArg(v_a_2622_);
return v___x_2623_;
}
else
{
lean_object* v_head_2624_; lean_object* v_tail_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2636_; 
v_head_2624_ = lean_ctor_get(v_a_2621_, 0);
v_tail_2625_ = lean_ctor_get(v_a_2621_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2621_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2627_ = v_a_2621_;
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_tail_2625_);
lean_inc(v_head_2624_);
lean_dec(v_a_2621_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2629_ = l_Nat_reprFast(v_head_2624_);
v___x_2630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = l_Lean_MessageData_ofFormat(v___x_2630_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 1, v_a_2622_);
lean_ctor_set(v___x_2627_, 0, v___x_2631_);
v___x_2633_ = v___x_2627_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_a_2622_);
v___x_2633_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
v_a_2621_ = v_tail_2625_;
v_a_2622_ = v___x_2633_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2637_; double v___x_2638_; 
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_float_of_nat(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2641_, lean_object* v_msg_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_ref_2648_; lean_object* v___x_2649_; lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2694_; 
v_ref_2648_ = lean_ctor_get(v___y_2645_, 5);
v___x_2649_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2694_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2694_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v_traceState_2655_; lean_object* v_env_2656_; lean_object* v_nextMacroScope_2657_; lean_object* v_ngen_2658_; lean_object* v_auxDeclNGen_2659_; lean_object* v_cache_2660_; lean_object* v_messages_2661_; lean_object* v_infoState_2662_; lean_object* v_snapshotTasks_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2693_; 
v___x_2654_ = lean_st_ref_take(v___y_2646_);
v_traceState_2655_ = lean_ctor_get(v___x_2654_, 4);
v_env_2656_ = lean_ctor_get(v___x_2654_, 0);
v_nextMacroScope_2657_ = lean_ctor_get(v___x_2654_, 1);
v_ngen_2658_ = lean_ctor_get(v___x_2654_, 2);
v_auxDeclNGen_2659_ = lean_ctor_get(v___x_2654_, 3);
v_cache_2660_ = lean_ctor_get(v___x_2654_, 5);
v_messages_2661_ = lean_ctor_get(v___x_2654_, 6);
v_infoState_2662_ = lean_ctor_get(v___x_2654_, 7);
v_snapshotTasks_2663_ = lean_ctor_get(v___x_2654_, 8);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2665_ = v___x_2654_;
v_isShared_2666_ = v_isSharedCheck_2693_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snapshotTasks_2663_);
lean_inc(v_infoState_2662_);
lean_inc(v_messages_2661_);
lean_inc(v_cache_2660_);
lean_inc(v_traceState_2655_);
lean_inc(v_auxDeclNGen_2659_);
lean_inc(v_ngen_2658_);
lean_inc(v_nextMacroScope_2657_);
lean_inc(v_env_2656_);
lean_dec(v___x_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2693_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint64_t v_tid_2667_; lean_object* v_traces_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2692_; 
v_tid_2667_ = lean_ctor_get_uint64(v_traceState_2655_, sizeof(void*)*1);
v_traces_2668_ = lean_ctor_get(v_traceState_2655_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_traceState_2655_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2670_ = v_traceState_2655_;
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_traces_2668_);
lean_dec(v_traceState_2655_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; double v___x_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2674_ = 0;
v___x_2675_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2676_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2676_, 0, v_cls_2641_);
lean_ctor_set(v___x_2676_, 1, v___x_2672_);
lean_ctor_set(v___x_2676_, 2, v___x_2675_);
lean_ctor_set_float(v___x_2676_, sizeof(void*)*3, v___x_2673_);
lean_ctor_set_float(v___x_2676_, sizeof(void*)*3 + 8, v___x_2673_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*3 + 16, v___x_2674_);
v___x_2677_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2678_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v_a_2650_);
lean_ctor_set(v___x_2678_, 2, v___x_2677_);
lean_inc(v_ref_2648_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_ref_2648_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_PersistentArray_push___redArg(v_traces_2668_, v___x_2679_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2680_);
v___x_2682_ = v___x_2670_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2680_);
lean_ctor_set_uint64(v_reuseFailAlloc_2691_, sizeof(void*)*1, v_tid_2667_);
v___x_2682_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2684_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 4, v___x_2682_);
v___x_2684_ = v___x_2665_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_env_2656_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_nextMacroScope_2657_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_ngen_2658_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_auxDeclNGen_2659_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v_cache_2660_);
lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_messages_2661_);
lean_ctor_set(v_reuseFailAlloc_2690_, 7, v_infoState_2662_);
lean_ctor_set(v_reuseFailAlloc_2690_, 8, v_snapshotTasks_2663_);
v___x_2684_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_st_ref_set(v___y_2646_, v___x_2684_);
v___x_2686_ = lean_box(0);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2686_);
v___x_2688_ = v___x_2652_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2695_, lean_object* v_msg_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2695_, v_msg_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
return v_res_2702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2712_ = l_Lean_Name_append(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2725_, lean_object* v_fst_2726_, lean_object* v_fst_2727_, lean_object* v_inst_2728_, lean_object* v_a_2729_, lean_object* v_projInfo_x3f_2730_, lean_object* v_argVars_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2725_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_dummy_2740_; lean_object* v_nargs_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; size_t v_sz_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___x_2738_);
v_dummy_2740_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2741_ = l_Lean_Expr_getAppNumArgs(v_a_2725_);
lean_inc(v_nargs_2741_);
v___x_2742_ = lean_mk_array(v_nargs_2741_, v_dummy_2740_);
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_nat_sub(v_nargs_2741_, v___x_2743_);
lean_dec(v_nargs_2741_);
lean_inc_ref(v_a_2725_);
v___x_2745_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2725_, v___x_2742_, v___x_2744_);
v___x_2746_ = lean_array_get_size(v___x_2745_);
v___x_2747_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___x_2746_);
v_sz_2749_ = lean_array_size(v___x_2745_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2739_, v_fst_2726_, v_argVars_2731_, v___x_2745_, v_sz_2749_, v___x_2750_, v___x_2748_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec_ref(v___x_2745_);
lean_dec(v_a_2739_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec_ref(v___x_2751_);
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2753_ = lean_array_get_size(v_fst_2726_);
v___x_2754_ = l_List_range(v___x_2753_);
v___x_2755_ = lean_box(0);
v___x_2756_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2727_, v___x_2754_, v___x_2755_);
v___x_2757_ = lean_array_mk(v___x_2756_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2752_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc_ref(v_inst_2728_);
v___x_2759_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2726_, v_argVars_2731_, v_inst_2728_, v_a_2729_, v_projInfo_x3f_2730_, v___x_2758_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2852_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2852_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2852_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_fst_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2850_; 
v_fst_2764_ = lean_ctor_get(v_a_2760_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; 
v_unused_2851_ = lean_ctor_get(v_a_2760_, 1);
lean_dec(v_unused_2851_);
v___x_2766_ = v_a_2760_;
v_isShared_2767_ = v_isSharedCheck_2850_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_fst_2764_);
lean_dec(v_a_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2850_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_options_2772_; lean_object* v_inheritedTraceOptions_2773_; lean_object* v___y_2774_; lean_object* v_options_2830_; lean_object* v_inheritedTraceOptions_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v_options_2830_ = lean_ctor_get(v___y_2735_, 2);
v_inheritedTraceOptions_2831_ = lean_ctor_get(v___y_2735_, 13);
v___x_2832_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2833_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2830_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_dec_ref(v_a_2725_);
v___y_2769_ = v___y_2733_;
v___y_2770_ = v___y_2734_;
v___y_2771_ = v___y_2735_;
v_options_2772_ = v_options_2830_;
v_inheritedTraceOptions_2773_ = v_inheritedTraceOptions_2831_;
v___y_2774_ = v___y_2736_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2834_; lean_object* v_a_2835_; uint8_t v___x_2836_; 
v___x_2834_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2725_, v___y_2734_);
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2834_);
v___x_2836_ = l_Lean_Expr_hasExprMVar(v_a_2835_);
if (v___x_2836_ == 0)
{
lean_dec(v_a_2835_);
v___y_2769_ = v___y_2733_;
v___y_2770_ = v___y_2734_;
v___y_2771_ = v___y_2735_;
v_options_2772_ = v_options_2830_;
v_inheritedTraceOptions_2773_ = v_inheritedTraceOptions_2831_;
v___y_2774_ = v___y_2736_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2766_);
lean_dec(v_fst_2764_);
lean_del_object(v___x_2762_);
lean_dec_ref(v_inst_2728_);
v___x_2837_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2838_ = l_Lean_Expr_setPPExplicit(v_a_2835_, v___x_2836_);
v___x_2839_ = l_Lean_indentExpr(v___x_2838_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2837_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2840_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
v___jp_2768_:
{
uint8_t v_hasTrace_2775_; 
v_hasTrace_2775_ = lean_ctor_get_uint8(v_options_2772_, sizeof(void*)*1);
if (v_hasTrace_2775_ == 0)
{
lean_object* v___x_2777_; 
lean_del_object(v___x_2766_);
lean_dec_ref(v_inst_2728_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_fst_2764_);
v___x_2777_ = v___x_2762_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_fst_2764_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2780_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2773_, v_options_2772_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2783_; 
lean_del_object(v___x_2766_);
lean_dec_ref(v_inst_2728_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_fst_2764_);
v___x_2783_ = v___x_2762_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_fst_2764_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
else
{
size_t v_sz_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2762_);
v_sz_2785_ = lean_array_size(v_fst_2764_);
lean_inc(v_fst_2764_);
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2731_, v_sz_2785_, v___x_2750_, v_fst_2764_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2774_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2789_ = l_Lean_MessageData_ofExpr(v_inst_2728_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 7);
lean_ctor_set(v___x_2766_, 1, v___x_2789_);
lean_ctor_set(v___x_2766_, 0, v___x_2788_);
v___x_2791_ = v___x_2766_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2792_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
lean_inc(v_fst_2764_);
v___x_2794_ = lean_array_to_list(v_fst_2764_);
v___x_2795_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2794_, v___x_2755_);
v___x_2796_ = l_Lean_MessageData_ofList(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_array_to_list(v_a_2787_);
v___x_2801_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2802_ = l_Lean_MessageData_joinSep(v___x_2800_, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2779_, v___x_2803_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2774_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___x_2804_, 0);
lean_dec(v_unused_2812_);
v___x_2806_ = v___x_2804_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v___x_2804_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_fst_2764_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_fst_2764_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_fst_2764_);
v_a_2813_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2804_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2804_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_del_object(v___x_2766_);
lean_dec(v_fst_2764_);
lean_dec_ref(v_inst_2728_);
v_a_2822_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2786_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2786_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
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
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v_inst_2728_);
lean_dec_ref(v_a_2725_);
v_a_2853_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2759_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2759_);
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
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref(v_a_2729_);
lean_dec_ref(v_inst_2728_);
lean_dec_ref(v_a_2725_);
v_a_2861_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2751_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2751_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_dec_ref(v_a_2729_);
lean_dec_ref(v_inst_2728_);
lean_dec_ref(v_a_2725_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2869_, lean_object* v_fst_2870_, lean_object* v_fst_2871_, lean_object* v_inst_2872_, lean_object* v_a_2873_, lean_object* v_projInfo_x3f_2874_, lean_object* v_argVars_2875_, lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2869_, v_fst_2870_, v_fst_2871_, v_inst_2872_, v_a_2873_, v_projInfo_x3f_2874_, v_argVars_2875_, v_x_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_x_2876_);
lean_dec_ref(v_argVars_2875_);
lean_dec(v_projInfo_x3f_2874_);
lean_dec_ref(v_fst_2871_);
lean_dec_ref(v_fst_2870_);
return v_res_2882_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2883_; uint64_t v___x_2884_; 
v___x_2883_ = 2;
v___x_2884_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2885_, lean_object* v_projInfo_x3f_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; uint8_t v_foApprox_2893_; uint8_t v_ctxApprox_2894_; uint8_t v_quasiPatternApprox_2895_; uint8_t v_constApprox_2896_; uint8_t v_isDefEqStuckEx_2897_; uint8_t v_unificationHints_2898_; uint8_t v_proofIrrelevance_2899_; uint8_t v_assignSyntheticOpaque_2900_; uint8_t v_offsetCnstrs_2901_; uint8_t v_etaStruct_2902_; uint8_t v_univApprox_2903_; uint8_t v_iota_2904_; uint8_t v_beta_2905_; uint8_t v_proj_2906_; uint8_t v_zeta_2907_; uint8_t v_zetaDelta_2908_; uint8_t v_zetaUnused_2909_; uint8_t v_zetaHave_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2975_; 
v___x_2892_ = l_Lean_Meta_Context_config(v_a_2887_);
v_foApprox_2893_ = lean_ctor_get_uint8(v___x_2892_, 0);
v_ctxApprox_2894_ = lean_ctor_get_uint8(v___x_2892_, 1);
v_quasiPatternApprox_2895_ = lean_ctor_get_uint8(v___x_2892_, 2);
v_constApprox_2896_ = lean_ctor_get_uint8(v___x_2892_, 3);
v_isDefEqStuckEx_2897_ = lean_ctor_get_uint8(v___x_2892_, 4);
v_unificationHints_2898_ = lean_ctor_get_uint8(v___x_2892_, 5);
v_proofIrrelevance_2899_ = lean_ctor_get_uint8(v___x_2892_, 6);
v_assignSyntheticOpaque_2900_ = lean_ctor_get_uint8(v___x_2892_, 7);
v_offsetCnstrs_2901_ = lean_ctor_get_uint8(v___x_2892_, 8);
v_etaStruct_2902_ = lean_ctor_get_uint8(v___x_2892_, 10);
v_univApprox_2903_ = lean_ctor_get_uint8(v___x_2892_, 11);
v_iota_2904_ = lean_ctor_get_uint8(v___x_2892_, 12);
v_beta_2905_ = lean_ctor_get_uint8(v___x_2892_, 13);
v_proj_2906_ = lean_ctor_get_uint8(v___x_2892_, 14);
v_zeta_2907_ = lean_ctor_get_uint8(v___x_2892_, 15);
v_zetaDelta_2908_ = lean_ctor_get_uint8(v___x_2892_, 16);
v_zetaUnused_2909_ = lean_ctor_get_uint8(v___x_2892_, 17);
v_zetaHave_2910_ = lean_ctor_get_uint8(v___x_2892_, 18);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2912_ = v___x_2892_;
v_isShared_2913_ = v_isSharedCheck_2975_;
goto v_resetjp_2911_;
}
else
{
lean_dec(v___x_2892_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2975_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
uint8_t v_trackZetaDelta_2914_; lean_object* v_zetaDeltaSet_2915_; lean_object* v_lctx_2916_; lean_object* v_localInstances_2917_; lean_object* v_defEqCtx_x3f_2918_; lean_object* v_synthPendingDepth_2919_; lean_object* v_canUnfold_x3f_2920_; uint8_t v_univApprox_2921_; uint8_t v_inTypeClassResolution_2922_; uint8_t v_cacheInferType_2923_; uint8_t v___x_2924_; lean_object* v_config_2926_; 
v_trackZetaDelta_2914_ = lean_ctor_get_uint8(v_a_2887_, sizeof(void*)*7);
v_zetaDeltaSet_2915_ = lean_ctor_get(v_a_2887_, 1);
v_lctx_2916_ = lean_ctor_get(v_a_2887_, 2);
v_localInstances_2917_ = lean_ctor_get(v_a_2887_, 3);
v_defEqCtx_x3f_2918_ = lean_ctor_get(v_a_2887_, 4);
v_synthPendingDepth_2919_ = lean_ctor_get(v_a_2887_, 5);
v_canUnfold_x3f_2920_ = lean_ctor_get(v_a_2887_, 6);
v_univApprox_2921_ = lean_ctor_get_uint8(v_a_2887_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2922_ = lean_ctor_get_uint8(v_a_2887_, sizeof(void*)*7 + 2);
v_cacheInferType_2923_ = lean_ctor_get_uint8(v_a_2887_, sizeof(void*)*7 + 3);
v___x_2924_ = 2;
if (v_isShared_2913_ == 0)
{
v_config_2926_ = v___x_2912_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 0, v_foApprox_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 1, v_ctxApprox_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 2, v_quasiPatternApprox_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 3, v_constApprox_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 4, v_isDefEqStuckEx_2897_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 5, v_unificationHints_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 6, v_proofIrrelevance_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 7, v_assignSyntheticOpaque_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 8, v_offsetCnstrs_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 10, v_etaStruct_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 11, v_univApprox_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 12, v_iota_2904_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 13, v_beta_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 14, v_proj_2906_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 15, v_zeta_2907_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 16, v_zetaDelta_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 17, v_zetaUnused_2909_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 18, v_zetaHave_2910_);
v_config_2926_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v___x_2929_; uint64_t v___x_2930_; uint64_t v___x_2931_; uint64_t v_key_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_ctor_set_uint8(v_config_2926_, 9, v___x_2924_);
v___x_2927_ = l_Lean_Meta_Context_configKey(v_a_2887_);
v___x_2928_ = 2ULL;
v___x_2929_ = lean_uint64_shift_right(v___x_2927_, v___x_2928_);
v___x_2930_ = lean_uint64_shift_left(v___x_2929_, v___x_2928_);
v___x_2931_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2932_ = lean_uint64_lor(v___x_2930_, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2933_, 0, v_config_2926_);
lean_ctor_set_uint64(v___x_2933_, sizeof(void*)*1, v_key_2932_);
lean_inc(v_canUnfold_x3f_2920_);
lean_inc(v_synthPendingDepth_2919_);
lean_inc(v_defEqCtx_x3f_2918_);
lean_inc_ref(v_localInstances_2917_);
lean_inc_ref(v_lctx_2916_);
lean_inc(v_zetaDeltaSet_2915_);
v___x_2934_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v_zetaDeltaSet_2915_);
lean_ctor_set(v___x_2934_, 2, v_lctx_2916_);
lean_ctor_set(v___x_2934_, 3, v_localInstances_2917_);
lean_ctor_set(v___x_2934_, 4, v_defEqCtx_x3f_2918_);
lean_ctor_set(v___x_2934_, 5, v_synthPendingDepth_2919_);
lean_ctor_set(v___x_2934_, 6, v_canUnfold_x3f_2920_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7, v_trackZetaDelta_2914_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 1, v_univApprox_2921_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2922_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 3, v_cacheInferType_2923_);
lean_inc(v_a_2890_);
lean_inc_ref(v_a_2889_);
lean_inc(v_a_2888_);
lean_inc_ref(v___x_2934_);
lean_inc_ref(v_inst_2885_);
v___x_2935_ = lean_infer_type(v_inst_2885_, v___x_2934_, v_a_2888_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_n(v_a_2936_, 2);
lean_dec_ref(v___x_2935_);
v___x_2937_ = lean_box(0);
v___x_2938_ = 0;
v___x_2939_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2936_, v___x_2937_, v___x_2938_, v___x_2934_, v_a_2888_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v_snd_2941_; lean_object* v_fst_2942_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v___x_2945_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v_snd_2941_ = lean_ctor_get(v_a_2940_, 1);
lean_inc(v_snd_2941_);
v_fst_2942_ = lean_ctor_get(v_a_2940_, 0);
lean_inc(v_fst_2942_);
lean_dec(v_a_2940_);
v_fst_2943_ = lean_ctor_get(v_snd_2941_, 0);
lean_inc(v_fst_2943_);
v_snd_2944_ = lean_ctor_get(v_snd_2941_, 1);
lean_inc(v_snd_2944_);
lean_dec(v_snd_2941_);
lean_inc(v_a_2890_);
lean_inc_ref(v_a_2889_);
lean_inc(v_a_2888_);
lean_inc_ref(v___x_2934_);
v___x_2945_ = lean_whnf(v_snd_2944_, v___x_2934_, v_a_2888_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___f_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
lean_inc(v_a_2936_);
v___f_2947_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2947_, 0, v_a_2946_);
lean_closure_set(v___f_2947_, 1, v_fst_2942_);
lean_closure_set(v___f_2947_, 2, v_fst_2943_);
lean_closure_set(v___f_2947_, 3, v_inst_2885_);
lean_closure_set(v___f_2947_, 4, v_a_2936_);
lean_closure_set(v___f_2947_, 5, v_projInfo_x3f_2886_);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2936_, v___f_2947_, v___x_2948_, v___x_2948_, v___x_2934_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec_ref(v___x_2934_);
return v___x_2949_;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_fst_2943_);
lean_dec(v_fst_2942_);
lean_dec(v_a_2936_);
lean_dec_ref(v___x_2934_);
lean_dec(v_projInfo_x3f_2886_);
lean_dec_ref(v_inst_2885_);
v_a_2950_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2945_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2945_);
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
lean_dec(v_a_2936_);
lean_dec_ref(v___x_2934_);
lean_dec(v_projInfo_x3f_2886_);
lean_dec_ref(v_inst_2885_);
v_a_2958_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2939_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2939_);
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
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v___x_2934_);
lean_dec(v_projInfo_x3f_2886_);
lean_dec_ref(v_inst_2885_);
v_a_2966_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2935_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2935_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_2976_, lean_object* v_projInfo_x3f_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_2976_, v_projInfo_x3f_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_2984_, lean_object* v___x_2985_, lean_object* v_a_2986_, lean_object* v_inst_2987_, lean_object* v_R_2988_, lean_object* v_a_2989_, lean_object* v_b_2990_, lean_object* v_c_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2984_, v___x_2985_, v_a_2986_, v_a_2989_, v_b_2990_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_2998_, lean_object* v___x_2999_, lean_object* v_a_3000_, lean_object* v_inst_3001_, lean_object* v_R_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_, lean_object* v_c_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_2998_, v___x_2999_, v_a_3000_, v_inst_3001_, v_R_3002_, v_a_3003_, v_b_3004_, v_c_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v_a_3000_);
lean_dec(v___x_2999_);
lean_dec(v_upperBound_2998_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3012_, lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3020_, lean_object* v_msg_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3020_, v_msg_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; lean_object* v_env_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = lean_st_ref_get(v___y_3029_);
v_env_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_ref(v_env_3032_);
lean_dec(v___x_3031_);
v___x_3033_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3032_, v_declName_3028_);
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3035_, v___y_3036_);
lean_dec(v___y_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3039_, v___y_3043_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3052_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3059_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
lean_ctor_set(v___x_3059_, 2, v___x_3058_);
lean_ctor_set(v___x_3059_, 3, v___x_3058_);
lean_ctor_set(v___x_3059_, 4, v___x_3058_);
lean_ctor_set(v___x_3059_, 5, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3060_, lean_object* v_b_3061_, uint8_t v_kind_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_currNamespace_3067_; lean_object* v___x_3068_; lean_object* v_env_3069_; lean_object* v_nextMacroScope_3070_; lean_object* v_ngen_3071_; lean_object* v_auxDeclNGen_3072_; lean_object* v_traceState_3073_; lean_object* v_messages_3074_; lean_object* v_infoState_3075_; lean_object* v_snapshotTasks_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3103_; 
v_currNamespace_3067_ = lean_ctor_get(v___y_3064_, 6);
v___x_3068_ = lean_st_ref_take(v___y_3065_);
v_env_3069_ = lean_ctor_get(v___x_3068_, 0);
v_nextMacroScope_3070_ = lean_ctor_get(v___x_3068_, 1);
v_ngen_3071_ = lean_ctor_get(v___x_3068_, 2);
v_auxDeclNGen_3072_ = lean_ctor_get(v___x_3068_, 3);
v_traceState_3073_ = lean_ctor_get(v___x_3068_, 4);
v_messages_3074_ = lean_ctor_get(v___x_3068_, 6);
v_infoState_3075_ = lean_ctor_get(v___x_3068_, 7);
v_snapshotTasks_3076_ = lean_ctor_get(v___x_3068_, 8);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v___x_3068_, 5);
lean_dec(v_unused_3104_);
v___x_3078_ = v___x_3068_;
v_isShared_3079_ = v_isSharedCheck_3103_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_snapshotTasks_3076_);
lean_inc(v_infoState_3075_);
lean_inc(v_messages_3074_);
lean_inc(v_traceState_3073_);
lean_inc(v_auxDeclNGen_3072_);
lean_inc(v_ngen_3071_);
lean_inc(v_nextMacroScope_3070_);
lean_inc(v_env_3069_);
lean_dec(v___x_3068_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3103_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
lean_inc(v_currNamespace_3067_);
v___x_3080_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3069_, v_ext_3060_, v_b_3061_, v_kind_3062_, v_currNamespace_3067_);
v___x_3081_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 5, v___x_3081_);
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3083_ = v___x_3078_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_nextMacroScope_3070_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_ngen_3071_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_auxDeclNGen_3072_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v_traceState_3073_);
lean_ctor_set(v_reuseFailAlloc_3102_, 5, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3102_, 6, v_messages_3074_);
lean_ctor_set(v_reuseFailAlloc_3102_, 7, v_infoState_3075_);
lean_ctor_set(v_reuseFailAlloc_3102_, 8, v_snapshotTasks_3076_);
v___x_3083_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_mctx_3086_; lean_object* v_zetaDeltaFVarIds_3087_; lean_object* v_postponed_3088_; lean_object* v_diag_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3100_; 
v___x_3084_ = lean_st_ref_set(v___y_3065_, v___x_3083_);
v___x_3085_ = lean_st_ref_take(v___y_3063_);
v_mctx_3086_ = lean_ctor_get(v___x_3085_, 0);
v_zetaDeltaFVarIds_3087_ = lean_ctor_get(v___x_3085_, 2);
v_postponed_3088_ = lean_ctor_get(v___x_3085_, 3);
v_diag_3089_ = lean_ctor_get(v___x_3085_, 4);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v___x_3085_, 1);
lean_dec(v_unused_3101_);
v___x_3091_ = v___x_3085_;
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_diag_3089_);
lean_inc(v_postponed_3088_);
lean_inc(v_zetaDeltaFVarIds_3087_);
lean_inc(v_mctx_3086_);
lean_dec(v___x_3085_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_mctx_3086_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_zetaDeltaFVarIds_3087_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_postponed_3088_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_diag_3089_);
v___x_3095_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = lean_st_ref_set(v___y_3063_, v___x_3095_);
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
return v___x_3098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3105_, lean_object* v_b_3106_, lean_object* v_kind_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
uint8_t v_kind_boxed_3112_; lean_object* v_res_3113_; 
v_kind_boxed_3112_ = lean_unbox(v_kind_3107_);
v_res_3113_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3105_, v_b_3106_, v_kind_boxed_3112_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3114_, lean_object* v_00_u03b2_3115_, lean_object* v_00_u03c3_3116_, lean_object* v_ext_3117_, lean_object* v_b_3118_, uint8_t v_kind_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3117_, v_b_3118_, v_kind_3119_, v___y_3121_, v___y_3122_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3126_, lean_object* v_00_u03b2_3127_, lean_object* v_00_u03c3_3128_, lean_object* v_ext_3129_, lean_object* v_b_3130_, lean_object* v_kind_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_kind_boxed_3137_; lean_object* v_res_3138_; 
v_kind_boxed_3137_ = lean_unbox(v_kind_3131_);
v_res_3138_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3126_, v_00_u03b2_3127_, v_00_u03c3_3128_, v_ext_3129_, v_b_3130_, v_kind_boxed_3137_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v_env_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3142_ = lean_st_ref_get(v___y_3140_);
v_env_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_env_3143_);
lean_dec(v___x_3142_);
v___x_3144_ = lean_get_reducibility_status(v_env_3143_, v_declName_3139_);
v___x_3145_ = lean_box(v___x_3144_);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3147_, v___y_3148_);
lean_dec(v___y_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3151_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
lean_ctor_set(v___x_3170_, 3, v___x_3169_);
lean_ctor_set(v___x_3170_, 4, v___x_3168_);
lean_ctor_set(v___x_3170_, 5, v___x_3168_);
lean_ctor_set(v___x_3170_, 6, v___x_3168_);
lean_ctor_set(v___x_3170_, 7, v___x_3168_);
lean_ctor_set(v___x_3170_, 8, v___x_3168_);
lean_ctor_set(v___x_3170_, 9, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_unsigned_to_nat(32u);
v___x_3172_ = lean_mk_empty_array_with_capacity(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3174_ = ((size_t)5ULL);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = lean_unsigned_to_nat(32u);
v___x_3177_ = lean_mk_empty_array_with_capacity(v___x_3176_);
v___x_3178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3179_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
lean_ctor_set(v___x_3179_, 2, v___x_3175_);
lean_ctor_set(v___x_3179_, 3, v___x_3175_);
lean_ctor_set_usize(v___x_3179_, 4, v___x_3174_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3180_ = lean_box(1);
v___x_3181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v___x_3181_);
lean_ctor_set(v___x_3183_, 2, v___x_3180_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3205_, lean_object* v_declHint_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; lean_object* v_env_3210_; uint8_t v___x_3211_; 
v___x_3209_ = lean_st_ref_get(v___y_3207_);
v_env_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_ref(v_env_3210_);
lean_dec(v___x_3209_);
v___x_3211_ = l_Lean_Name_isAnonymous(v_declHint_3206_);
if (v___x_3211_ == 0)
{
uint8_t v_isExporting_3212_; 
v_isExporting_3212_ = lean_ctor_get_uint8(v_env_3210_, sizeof(void*)*8);
if (v_isExporting_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v_env_3210_);
lean_dec(v_declHint_3206_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v_msg_3205_);
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
lean_inc_ref(v_env_3210_);
v___x_3214_ = l_Lean_Environment_setExporting(v_env_3210_, v___x_3211_);
lean_inc(v_declHint_3206_);
lean_inc_ref(v___x_3214_);
v___x_3215_ = l_Lean_Environment_contains(v___x_3214_, v_declHint_3206_, v_isExporting_3212_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; 
lean_dec_ref(v___x_3214_);
lean_dec_ref(v_env_3210_);
lean_dec(v_declHint_3206_);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_msg_3205_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v_c_3222_; lean_object* v___x_3223_; 
v___x_3217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3218_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3219_ = l_Lean_Options_empty;
v___x_3220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3214_);
lean_ctor_set(v___x_3220_, 1, v___x_3217_);
lean_ctor_set(v___x_3220_, 2, v___x_3218_);
lean_ctor_set(v___x_3220_, 3, v___x_3219_);
lean_inc(v_declHint_3206_);
v___x_3221_ = l_Lean_MessageData_ofConstName(v_declHint_3206_, v___x_3211_);
v_c_3222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3222_, 0, v___x_3220_);
lean_ctor_set(v_c_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3210_, v_declHint_3206_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v_env_3210_);
lean_dec(v_declHint_3206_);
v___x_3224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v_c_3222_);
v___x_3226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3225_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = l_Lean_MessageData_note(v___x_3227_);
v___x_3229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_msg_3205_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
else
{
lean_object* v_val_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3266_; 
v_val_3231_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3233_ = v___x_3223_;
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_val_3231_);
lean_dec(v___x_3223_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_mod_3238_; uint8_t v___x_3239_; 
v___x_3235_ = lean_box(0);
v___x_3236_ = l_Lean_Environment_header(v_env_3210_);
lean_dec_ref(v_env_3210_);
v___x_3237_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3236_);
v_mod_3238_ = lean_array_get(v___x_3235_, v___x_3237_, v_val_3231_);
lean_dec(v_val_3231_);
lean_dec_ref(v___x_3237_);
v___x_3239_ = l_Lean_isPrivateName(v_declHint_3206_);
lean_dec(v_declHint_3206_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v_c_3222_);
v___x_3242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_MessageData_ofName(v_mod_3238_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_MessageData_note(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_msg_3205_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3249_);
v___x_3251_ = v___x_3233_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set(v___x_3254_, 1, v_c_3222_);
v___x_3255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_MessageData_ofName(v_mod_3238_);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_MessageData_note(v___x_3260_);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_msg_3205_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3262_);
v___x_3264_ = v___x_3233_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3267_; 
lean_dec_ref(v_env_3210_);
lean_dec(v_declHint_3206_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_msg_3205_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3268_, lean_object* v_declHint_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3268_, v_declHint_3269_, v___y_3270_);
lean_dec(v___y_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3273_, lean_object* v_declHint_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3290_; 
v___x_3280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3273_, v_declHint_3274_, v___y_3278_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3290_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3290_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3285_ = l_Lean_unknownIdentifierMessageTag;
v___x_3286_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v_a_3281_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3286_);
v___x_3288_ = v___x_3283_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3291_, lean_object* v_declHint_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3291_, v_declHint_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3299_, lean_object* v_msg_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_fileName_3306_; lean_object* v_fileMap_3307_; lean_object* v_options_3308_; lean_object* v_currRecDepth_3309_; lean_object* v_maxRecDepth_3310_; lean_object* v_ref_3311_; lean_object* v_currNamespace_3312_; lean_object* v_openDecls_3313_; lean_object* v_initHeartbeats_3314_; lean_object* v_maxHeartbeats_3315_; lean_object* v_quotContext_3316_; lean_object* v_currMacroScope_3317_; uint8_t v_diag_3318_; lean_object* v_cancelTk_x3f_3319_; uint8_t v_suppressElabErrors_3320_; lean_object* v_inheritedTraceOptions_3321_; lean_object* v_ref_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_fileName_3306_ = lean_ctor_get(v___y_3303_, 0);
v_fileMap_3307_ = lean_ctor_get(v___y_3303_, 1);
v_options_3308_ = lean_ctor_get(v___y_3303_, 2);
v_currRecDepth_3309_ = lean_ctor_get(v___y_3303_, 3);
v_maxRecDepth_3310_ = lean_ctor_get(v___y_3303_, 4);
v_ref_3311_ = lean_ctor_get(v___y_3303_, 5);
v_currNamespace_3312_ = lean_ctor_get(v___y_3303_, 6);
v_openDecls_3313_ = lean_ctor_get(v___y_3303_, 7);
v_initHeartbeats_3314_ = lean_ctor_get(v___y_3303_, 8);
v_maxHeartbeats_3315_ = lean_ctor_get(v___y_3303_, 9);
v_quotContext_3316_ = lean_ctor_get(v___y_3303_, 10);
v_currMacroScope_3317_ = lean_ctor_get(v___y_3303_, 11);
v_diag_3318_ = lean_ctor_get_uint8(v___y_3303_, sizeof(void*)*14);
v_cancelTk_x3f_3319_ = lean_ctor_get(v___y_3303_, 12);
v_suppressElabErrors_3320_ = lean_ctor_get_uint8(v___y_3303_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3321_ = lean_ctor_get(v___y_3303_, 13);
v_ref_3322_ = l_Lean_replaceRef(v_ref_3299_, v_ref_3311_);
lean_inc_ref(v_inheritedTraceOptions_3321_);
lean_inc(v_cancelTk_x3f_3319_);
lean_inc(v_currMacroScope_3317_);
lean_inc(v_quotContext_3316_);
lean_inc(v_maxHeartbeats_3315_);
lean_inc(v_initHeartbeats_3314_);
lean_inc(v_openDecls_3313_);
lean_inc(v_currNamespace_3312_);
lean_inc(v_maxRecDepth_3310_);
lean_inc(v_currRecDepth_3309_);
lean_inc_ref(v_options_3308_);
lean_inc_ref(v_fileMap_3307_);
lean_inc_ref(v_fileName_3306_);
v___x_3323_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3323_, 0, v_fileName_3306_);
lean_ctor_set(v___x_3323_, 1, v_fileMap_3307_);
lean_ctor_set(v___x_3323_, 2, v_options_3308_);
lean_ctor_set(v___x_3323_, 3, v_currRecDepth_3309_);
lean_ctor_set(v___x_3323_, 4, v_maxRecDepth_3310_);
lean_ctor_set(v___x_3323_, 5, v_ref_3322_);
lean_ctor_set(v___x_3323_, 6, v_currNamespace_3312_);
lean_ctor_set(v___x_3323_, 7, v_openDecls_3313_);
lean_ctor_set(v___x_3323_, 8, v_initHeartbeats_3314_);
lean_ctor_set(v___x_3323_, 9, v_maxHeartbeats_3315_);
lean_ctor_set(v___x_3323_, 10, v_quotContext_3316_);
lean_ctor_set(v___x_3323_, 11, v_currMacroScope_3317_);
lean_ctor_set(v___x_3323_, 12, v_cancelTk_x3f_3319_);
lean_ctor_set(v___x_3323_, 13, v_inheritedTraceOptions_3321_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*14, v_diag_3318_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*14 + 1, v_suppressElabErrors_3320_);
v___x_3324_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3300_, v___y_3301_, v___y_3302_, v___x_3323_, v___y_3304_);
lean_dec_ref(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3325_, lean_object* v_msg_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3325_, v_msg_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v_ref_3325_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3333_, lean_object* v_msg_3334_, lean_object* v_declHint_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; lean_object* v_a_3342_; lean_object* v___x_3343_; 
v___x_3341_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3334_, v_declHint_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref(v___x_3341_);
v___x_3343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3333_, v_a_3342_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3344_, lean_object* v_msg_3345_, lean_object* v_declHint_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3344_, v_msg_3345_, v_declHint_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v_ref_3344_);
return v_res_3352_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3355_ = l_Lean_stringToMessageData(v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3356_, lean_object* v_constName_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3363_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3364_ = 0;
lean_inc(v_constName_3357_);
v___x_3365_ = l_Lean_MessageData_ofConstName(v_constName_3357_, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3363_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3356_, v___x_3368_, v_constName_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3370_, lean_object* v_constName_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3370_, v_constName_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v_ref_3370_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_ref_3384_; lean_object* v___x_3385_; 
v_ref_3384_ = lean_ctor_get(v___y_3381_, 5);
v___x_3385_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3384_, v_constName_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v_env_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_st_ref_get(v___y_3397_);
v_env_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc_ref(v_env_3400_);
lean_dec(v___x_3399_);
v___x_3401_ = 0;
lean_inc(v_constName_3393_);
v___x_3402_ = l_Lean_Environment_find_x3f(v_env_3400_, v_constName_3393_, v___x_3401_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3403_;
}
else
{
lean_object* v_val_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_constName_3393_);
v_val_3404_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3402_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_val_3404_);
lean_dec(v___x_3402_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 0);
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_val_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3418_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3426_, uint8_t v_suppressElabErrors_3427_, lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 1)
{
lean_object* v_pre_3429_; 
v_pre_3429_ = lean_ctor_get(v_x_3428_, 0);
switch(lean_obj_tag(v_pre_3429_))
{
case 1:
{
lean_object* v_pre_3430_; 
v_pre_3430_ = lean_ctor_get(v_pre_3429_, 0);
switch(lean_obj_tag(v_pre_3430_))
{
case 0:
{
lean_object* v_str_3431_; lean_object* v_str_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_str_3431_ = lean_ctor_get(v_x_3428_, 1);
v_str_3432_ = lean_ctor_get(v_pre_3429_, 1);
v___x_3433_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3434_ = lean_string_dec_eq(v_str_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3436_ = lean_string_dec_eq(v_str_3432_, v___x_3435_);
if (v___x_3436_ == 0)
{
return v___y_3426_;
}
else
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3438_ = lean_string_dec_eq(v_str_3431_, v___x_3437_);
if (v___x_3438_ == 0)
{
return v___y_3426_;
}
else
{
return v_suppressElabErrors_3427_;
}
}
}
else
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3440_ = lean_string_dec_eq(v_str_3431_, v___x_3439_);
if (v___x_3440_ == 0)
{
return v___y_3426_;
}
else
{
return v_suppressElabErrors_3427_;
}
}
}
case 1:
{
lean_object* v_pre_3441_; 
v_pre_3441_ = lean_ctor_get(v_pre_3430_, 0);
if (lean_obj_tag(v_pre_3441_) == 0)
{
lean_object* v_str_3442_; lean_object* v_str_3443_; lean_object* v_str_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_str_3442_ = lean_ctor_get(v_x_3428_, 1);
v_str_3443_ = lean_ctor_get(v_pre_3429_, 1);
v_str_3444_ = lean_ctor_get(v_pre_3430_, 1);
v___x_3445_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3446_ = lean_string_dec_eq(v_str_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
return v___y_3426_;
}
else
{
lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3448_ = lean_string_dec_eq(v_str_3443_, v___x_3447_);
if (v___x_3448_ == 0)
{
return v___y_3426_;
}
else
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3450_ = lean_string_dec_eq(v_str_3442_, v___x_3449_);
if (v___x_3450_ == 0)
{
return v___y_3426_;
}
else
{
return v_suppressElabErrors_3427_;
}
}
}
}
else
{
return v___y_3426_;
}
}
default: 
{
return v___y_3426_;
}
}
}
case 0:
{
lean_object* v_str_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_str_3451_ = lean_ctor_get(v_x_3428_, 1);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3453_ = lean_string_dec_eq(v_str_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
return v___y_3426_;
}
else
{
return v_suppressElabErrors_3427_;
}
}
default: 
{
return v___y_3426_;
}
}
}
else
{
return v___y_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3454_, lean_object* v_suppressElabErrors_3455_, lean_object* v_x_3456_){
_start:
{
uint8_t v___y_8288__boxed_3457_; uint8_t v_suppressElabErrors_boxed_3458_; uint8_t v_res_3459_; lean_object* v_r_3460_; 
v___y_8288__boxed_3457_ = lean_unbox(v___y_3454_);
v_suppressElabErrors_boxed_3458_ = lean_unbox(v_suppressElabErrors_3455_);
v_res_3459_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8288__boxed_3457_, v_suppressElabErrors_boxed_3458_, v_x_3456_);
lean_dec(v_x_3456_);
v_r_3460_ = lean_box(v_res_3459_);
return v_r_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3461_, lean_object* v_msgData_3462_, uint8_t v_severity_3463_, uint8_t v_isSilent_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3507_; uint8_t v___y_3508_; uint8_t v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; uint8_t v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3543_; uint8_t v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; uint8_t v___y_3549_; uint8_t v___x_3554_; uint8_t v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; uint8_t v___y_3562_; uint8_t v___y_3564_; uint8_t v___x_3579_; 
v___x_3554_ = 2;
v___x_3579_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3463_, v___x_3554_);
if (v___x_3579_ == 0)
{
v___y_3564_ = v___x_3579_;
goto v___jp_3563_;
}
else
{
uint8_t v___x_3580_; 
lean_inc_ref(v_msgData_3462_);
v___x_3580_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3462_);
v___y_3564_ = v___x_3580_;
goto v___jp_3563_;
}
v___jp_3470_:
{
lean_object* v___x_3480_; lean_object* v_currNamespace_3481_; lean_object* v_openDecls_3482_; lean_object* v_env_3483_; lean_object* v_nextMacroScope_3484_; lean_object* v_ngen_3485_; lean_object* v_auxDeclNGen_3486_; lean_object* v_traceState_3487_; lean_object* v_cache_3488_; lean_object* v_messages_3489_; lean_object* v_infoState_3490_; lean_object* v_snapshotTasks_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3505_; 
v___x_3480_ = lean_st_ref_take(v___y_3479_);
v_currNamespace_3481_ = lean_ctor_get(v___y_3478_, 6);
v_openDecls_3482_ = lean_ctor_get(v___y_3478_, 7);
v_env_3483_ = lean_ctor_get(v___x_3480_, 0);
v_nextMacroScope_3484_ = lean_ctor_get(v___x_3480_, 1);
v_ngen_3485_ = lean_ctor_get(v___x_3480_, 2);
v_auxDeclNGen_3486_ = lean_ctor_get(v___x_3480_, 3);
v_traceState_3487_ = lean_ctor_get(v___x_3480_, 4);
v_cache_3488_ = lean_ctor_get(v___x_3480_, 5);
v_messages_3489_ = lean_ctor_get(v___x_3480_, 6);
v_infoState_3490_ = lean_ctor_get(v___x_3480_, 7);
v_snapshotTasks_3491_ = lean_ctor_get(v___x_3480_, 8);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3493_ = v___x_3480_;
v_isShared_3494_ = v_isSharedCheck_3505_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snapshotTasks_3491_);
lean_inc(v_infoState_3490_);
lean_inc(v_messages_3489_);
lean_inc(v_cache_3488_);
lean_inc(v_traceState_3487_);
lean_inc(v_auxDeclNGen_3486_);
lean_inc(v_ngen_3485_);
lean_inc(v_nextMacroScope_3484_);
lean_inc(v_env_3483_);
lean_dec(v___x_3480_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3505_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_inc(v_openDecls_3482_);
lean_inc(v_currNamespace_3481_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_currNamespace_3481_);
lean_ctor_set(v___x_3495_, 1, v_openDecls_3482_);
v___x_3496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___y_3472_);
lean_inc_ref(v___y_3473_);
lean_inc_ref(v___y_3477_);
v___x_3497_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3497_, 0, v___y_3477_);
lean_ctor_set(v___x_3497_, 1, v___y_3471_);
lean_ctor_set(v___x_3497_, 2, v___y_3475_);
lean_ctor_set(v___x_3497_, 3, v___y_3473_);
lean_ctor_set(v___x_3497_, 4, v___x_3496_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*5, v___y_3476_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*5 + 1, v___y_3474_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*5 + 2, v_isSilent_3464_);
v___x_3498_ = l_Lean_MessageLog_add(v___x_3497_, v_messages_3489_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 6, v___x_3498_);
v___x_3500_ = v___x_3493_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_env_3483_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_nextMacroScope_3484_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v_ngen_3485_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_auxDeclNGen_3486_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_traceState_3487_);
lean_ctor_set(v_reuseFailAlloc_3504_, 5, v_cache_3488_);
lean_ctor_set(v_reuseFailAlloc_3504_, 6, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3504_, 7, v_infoState_3490_);
lean_ctor_set(v_reuseFailAlloc_3504_, 8, v_snapshotTasks_3491_);
v___x_3500_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_st_ref_set(v___y_3479_, v___x_3500_);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
return v___x_3503_;
}
}
}
v___jp_3506_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3530_; 
v___x_3515_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3462_);
v___x_3516_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3515_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_inc_ref_n(v___y_3512_, 2);
v___x_3521_ = l_Lean_FileMap_toPosition(v___y_3512_, v___y_3511_);
lean_dec(v___y_3511_);
v___x_3522_ = l_Lean_FileMap_toPosition(v___y_3512_, v___y_3514_);
lean_dec(v___y_3514_);
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
v___x_3524_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3509_ == 0)
{
lean_del_object(v___x_3519_);
lean_dec_ref(v___y_3507_);
v___y_3471_ = v___x_3521_;
v___y_3472_ = v_a_3517_;
v___y_3473_ = v___x_3524_;
v___y_3474_ = v___y_3508_;
v___y_3475_ = v___x_3523_;
v___y_3476_ = v___y_3510_;
v___y_3477_ = v___y_3513_;
v___y_3478_ = v___y_3467_;
v___y_3479_ = v___y_3468_;
goto v___jp_3470_;
}
else
{
uint8_t v___x_3525_; 
lean_inc(v_a_3517_);
v___x_3525_ = l_Lean_MessageData_hasTag(v___y_3507_, v_a_3517_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
lean_dec_ref(v___x_3523_);
lean_dec_ref(v___x_3521_);
lean_dec(v_a_3517_);
v___x_3526_ = lean_box(0);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3526_);
v___x_3528_ = v___x_3519_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_del_object(v___x_3519_);
v___y_3471_ = v___x_3521_;
v___y_3472_ = v_a_3517_;
v___y_3473_ = v___x_3524_;
v___y_3474_ = v___y_3508_;
v___y_3475_ = v___x_3523_;
v___y_3476_ = v___y_3510_;
v___y_3477_ = v___y_3513_;
v___y_3478_ = v___y_3467_;
v___y_3479_ = v___y_3468_;
goto v___jp_3470_;
}
}
}
}
v___jp_3531_:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Syntax_getTailPos_x3f(v___y_3533_, v___y_3536_);
lean_dec(v___y_3533_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_inc(v___y_3539_);
v___y_3507_ = v___y_3532_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3536_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3537_;
v___y_3513_ = v___y_3538_;
v___y_3514_ = v___y_3539_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3541_; 
v_val_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_val_3541_);
lean_dec_ref(v___x_3540_);
v___y_3507_ = v___y_3532_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3536_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3537_;
v___y_3513_ = v___y_3538_;
v___y_3514_ = v_val_3541_;
goto v___jp_3506_;
}
}
v___jp_3542_:
{
lean_object* v_ref_3550_; lean_object* v___x_3551_; 
v_ref_3550_ = l_Lean_replaceRef(v_ref_3461_, v___y_3545_);
v___x_3551_ = l_Lean_Syntax_getPos_x3f(v_ref_3550_, v___y_3546_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_unsigned_to_nat(0u);
v___y_3532_ = v___y_3543_;
v___y_3533_ = v_ref_3550_;
v___y_3534_ = v___y_3549_;
v___y_3535_ = v___y_3544_;
v___y_3536_ = v___y_3546_;
v___y_3537_ = v___y_3547_;
v___y_3538_ = v___y_3548_;
v___y_3539_ = v___x_3552_;
goto v___jp_3531_;
}
else
{
lean_object* v_val_3553_; 
v_val_3553_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_val_3553_);
lean_dec_ref(v___x_3551_);
v___y_3532_ = v___y_3543_;
v___y_3533_ = v_ref_3550_;
v___y_3534_ = v___y_3549_;
v___y_3535_ = v___y_3544_;
v___y_3536_ = v___y_3546_;
v___y_3537_ = v___y_3547_;
v___y_3538_ = v___y_3548_;
v___y_3539_ = v_val_3553_;
goto v___jp_3531_;
}
}
v___jp_3555_:
{
if (v___y_3562_ == 0)
{
v___y_3543_ = v___y_3558_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3557_;
v___y_3546_ = v___y_3561_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v___y_3560_;
v___y_3549_ = v_severity_3463_;
goto v___jp_3542_;
}
else
{
v___y_3543_ = v___y_3558_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3557_;
v___y_3546_ = v___y_3561_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v___y_3560_;
v___y_3549_ = v___x_3554_;
goto v___jp_3542_;
}
}
v___jp_3563_:
{
if (v___y_3564_ == 0)
{
lean_object* v_fileName_3565_; lean_object* v_fileMap_3566_; lean_object* v_options_3567_; lean_object* v_ref_3568_; uint8_t v_suppressElabErrors_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; uint8_t v___x_3573_; uint8_t v___x_3574_; 
v_fileName_3565_ = lean_ctor_get(v___y_3467_, 0);
v_fileMap_3566_ = lean_ctor_get(v___y_3467_, 1);
v_options_3567_ = lean_ctor_get(v___y_3467_, 2);
v_ref_3568_ = lean_ctor_get(v___y_3467_, 5);
v_suppressElabErrors_3569_ = lean_ctor_get_uint8(v___y_3467_, sizeof(void*)*14 + 1);
v___x_3570_ = lean_box(v___y_3564_);
v___x_3571_ = lean_box(v_suppressElabErrors_3569_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3572_, 0, v___x_3570_);
lean_closure_set(v___f_3572_, 1, v___x_3571_);
v___x_3573_ = 1;
v___x_3574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3463_, v___x_3573_);
if (v___x_3574_ == 0)
{
v___y_3556_ = v_suppressElabErrors_3569_;
v___y_3557_ = v_ref_3568_;
v___y_3558_ = v___f_3572_;
v___y_3559_ = v_fileMap_3566_;
v___y_3560_ = v_fileName_3565_;
v___y_3561_ = v___y_3564_;
v___y_3562_ = v___x_3574_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = l_Lean_warningAsError;
v___x_3576_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3567_, v___x_3575_);
v___y_3556_ = v_suppressElabErrors_3569_;
v___y_3557_ = v_ref_3568_;
v___y_3558_ = v___f_3572_;
v___y_3559_ = v_fileMap_3566_;
v___y_3560_ = v_fileName_3565_;
v___y_3561_ = v___y_3564_;
v___y_3562_ = v___x_3576_;
goto v___jp_3555_;
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v_msgData_3462_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3581_, lean_object* v_msgData_3582_, lean_object* v_severity_3583_, lean_object* v_isSilent_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v_severity_boxed_3590_; uint8_t v_isSilent_boxed_3591_; lean_object* v_res_3592_; 
v_severity_boxed_3590_ = lean_unbox(v_severity_3583_);
v_isSilent_boxed_3591_ = lean_unbox(v_isSilent_3584_);
v_res_3592_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3581_, v_msgData_3582_, v_severity_boxed_3590_, v_isSilent_boxed_3591_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_ref_3581_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3593_, uint8_t v_severity_3594_, uint8_t v_isSilent_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_ref_3601_; lean_object* v___x_3602_; 
v_ref_3601_ = lean_ctor_get(v___y_3598_, 5);
v___x_3602_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3601_, v_msgData_3593_, v_severity_3594_, v_isSilent_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3603_, lean_object* v_severity_3604_, lean_object* v_isSilent_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
uint8_t v_severity_boxed_3611_; uint8_t v_isSilent_boxed_3612_; lean_object* v_res_3613_; 
v_severity_boxed_3611_ = lean_unbox(v_severity_3604_);
v_isSilent_boxed_3612_ = lean_unbox(v_isSilent_3605_);
v_res_3613_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3603_, v_severity_boxed_3611_, v_isSilent_boxed_3612_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = 1;
v___x_3621_ = 0;
v___x_3622_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3614_, v___x_3620_, v___x_3621_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v_env_3637_; uint8_t v___x_3638_; lean_object* v___x_3639_; 
v___x_3636_ = lean_st_ref_get(v___y_3634_);
v_env_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc_ref(v_env_3637_);
lean_dec(v___x_3636_);
v___x_3638_ = 0;
lean_inc(v_constName_3630_);
v___x_3639_ = l_Lean_Environment_findConstVal_x3f(v_env_3637_, v_constName_3630_, v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
return v___x_3640_;
}
else
{
lean_object* v_val_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec(v_constName_3630_);
v_val_3641_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3639_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_val_3641_);
lean_dec(v___x_3639_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 0);
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_val_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
if (lean_obj_tag(v_a_3656_) == 0)
{
lean_object* v___x_3658_; 
v___x_3658_ = l_List_reverse___redArg(v_a_3657_);
return v___x_3658_;
}
else
{
lean_object* v_head_3659_; lean_object* v_tail_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3669_; 
v_head_3659_ = lean_ctor_get(v_a_3656_, 0);
v_tail_3660_ = lean_ctor_get(v_a_3656_, 1);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_a_3656_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3662_ = v_a_3656_;
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_tail_3660_);
lean_inc(v_head_3659_);
lean_dec(v_a_3656_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = l_Lean_mkLevelParam(v_head_3659_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v_a_3657_);
lean_ctor_set(v___x_3662_, 0, v___x_3664_);
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_a_3657_);
v___x_3666_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
v_a_3656_ = v_tail_3660_;
v_a_3657_ = v___x_3666_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
lean_inc(v_constName_3670_);
v___x_3676_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3688_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3688_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3688_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_levelParams_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
v_levelParams_3681_ = lean_ctor_get(v_a_3677_, 1);
lean_inc(v_levelParams_3681_);
lean_dec(v_a_3677_);
v___x_3682_ = lean_box(0);
v___x_3683_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_3681_, v___x_3682_);
v___x_3684_ = l_Lean_mkConst(v_constName_3670_, v___x_3683_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3684_);
v___x_3686_ = v___x_3679_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_constName_3670_);
v_a_3689_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3676_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3676_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3703_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_3706_ = l_Lean_stringToMessageData(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_3713_, uint8_t v_attrKind_3714_, lean_object* v_prio_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3721_; 
lean_inc(v_declName_3713_);
v___x_3721_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_3713_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3723_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc_n(v_a_3722_, 2);
lean_dec_ref(v___x_3721_);
v___x_3723_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_3722_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___x_3752_; lean_object* v_a_3753_; uint8_t v___x_3754_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref(v___x_3723_);
lean_inc(v_declName_3713_);
v___x_3752_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3713_, v_a_3719_);
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = lean_unbox(v_a_3753_);
lean_dec(v_a_3753_);
switch(v___x_3754_)
{
case 0:
{
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
v___y_3729_ = v_a_3719_;
goto v___jp_3725_;
}
case 3:
{
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
v___y_3729_ = v_a_3719_;
goto v___jp_3725_;
}
default: 
{
lean_object* v___x_3755_; 
lean_inc(v_declName_3713_);
v___x_3755_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_3713_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; uint8_t v___x_3757_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = l_Lean_ConstantInfo_isDefinition(v_a_3756_);
lean_dec(v_a_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; lean_object* v_env_3759_; uint8_t v___x_3760_; 
v___x_3758_ = lean_st_ref_get(v_a_3719_);
v_env_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc_ref(v_env_3759_);
lean_dec(v___x_3758_);
lean_inc(v_declName_3713_);
v___x_3760_ = l_Lean_wasOriginallyDefn(v_env_3759_, v_declName_3713_);
if (v___x_3760_ == 0)
{
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
v___y_3729_ = v_a_3719_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3761_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3713_);
v___x_3762_ = l_Lean_MessageData_ofName(v_declName_3713_);
v___x_3763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3765_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_dec_ref(v___x_3766_);
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
v___y_3729_ = v_a_3719_;
goto v___jp_3725_;
}
else
{
lean_dec(v_a_3724_);
lean_dec(v_a_3722_);
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
return v___x_3766_;
}
}
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3767_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3713_);
v___x_3768_ = l_Lean_MessageData_ofName(v_declName_3713_);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3771_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_dec_ref(v___x_3772_);
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
v___y_3729_ = v_a_3719_;
goto v___jp_3725_;
}
else
{
lean_dec(v_a_3724_);
lean_dec(v_a_3722_);
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
return v___x_3772_;
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v_a_3724_);
lean_dec(v_a_3722_);
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
v_a_3773_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3755_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3755_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
v___jp_3725_:
{
lean_object* v___x_3730_; lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3751_; 
lean_inc(v_declName_3713_);
v___x_3730_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3713_, v___y_3729_);
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3751_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3751_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; 
lean_inc(v_a_3722_);
v___x_3735_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_3722_, v_a_3731_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = l_Lean_Meta_instanceExtension;
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
lean_ctor_set(v___x_3733_, 0, v_declName_3713_);
v___x_3739_ = v___x_3733_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_declName_3713_);
v___x_3739_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3740_, 0, v_a_3724_);
lean_ctor_set(v___x_3740_, 1, v_a_3722_);
lean_ctor_set(v___x_3740_, 2, v_prio_3715_);
lean_ctor_set(v___x_3740_, 3, v___x_3739_);
lean_ctor_set(v___x_3740_, 4, v_a_3736_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*5, v_attrKind_3714_);
v___x_3741_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_3737_, v___x_3740_, v_attrKind_3714_, v___y_3727_, v___y_3728_, v___y_3729_);
return v___x_3741_;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3733_);
lean_dec(v_a_3724_);
lean_dec(v_a_3722_);
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
v_a_3743_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3735_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3735_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_a_3722_);
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
v_a_3781_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3723_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3723_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v_prio_3715_);
lean_dec(v_declName_3713_);
v_a_3789_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3721_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3721_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_3797_, lean_object* v_attrKind_3798_, lean_object* v_prio_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
uint8_t v_attrKind_boxed_3805_; lean_object* v_res_3806_; 
v_attrKind_boxed_3805_ = lean_unbox(v_attrKind_3798_);
v_res_3806_ = l_Lean_Meta_addInstance(v_declName_3797_, v_attrKind_boxed_3805_, v_prio_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_3807_, lean_object* v_constName_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3815_, lean_object* v_constName_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_3815_, v_constName_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_3823_, lean_object* v_ref_3824_, lean_object* v_constName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3824_, v_constName_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_3832_, lean_object* v_ref_3833_, lean_object* v_constName_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_3832_, v_ref_3833_, v_constName_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v_ref_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_3841_, lean_object* v_ref_3842_, lean_object* v_msg_3843_, lean_object* v_declHint_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3842_, v_msg_3843_, v_declHint_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3851_, lean_object* v_ref_3852_, lean_object* v_msg_3853_, lean_object* v_declHint_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_3851_, v_ref_3852_, v_msg_3853_, v_declHint_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v_ref_3852_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_3861_, lean_object* v_declHint_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3861_, v_declHint_3862_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_3869_, lean_object* v_declHint_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_3869_, v_declHint_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_3877_, lean_object* v_ref_3878_, lean_object* v_msg_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3878_, v_msg_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3886_, lean_object* v_ref_3887_, lean_object* v_msg_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_3886_, v_ref_3887_, v_msg_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v_ref_3887_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_3895_, uint8_t v_s_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; lean_object* v_env_3901_; lean_object* v_nextMacroScope_3902_; lean_object* v_ngen_3903_; lean_object* v_auxDeclNGen_3904_; lean_object* v_traceState_3905_; lean_object* v_messages_3906_; lean_object* v_infoState_3907_; lean_object* v_snapshotTasks_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3937_; 
v___x_3900_ = lean_st_ref_take(v___y_3898_);
v_env_3901_ = lean_ctor_get(v___x_3900_, 0);
v_nextMacroScope_3902_ = lean_ctor_get(v___x_3900_, 1);
v_ngen_3903_ = lean_ctor_get(v___x_3900_, 2);
v_auxDeclNGen_3904_ = lean_ctor_get(v___x_3900_, 3);
v_traceState_3905_ = lean_ctor_get(v___x_3900_, 4);
v_messages_3906_ = lean_ctor_get(v___x_3900_, 6);
v_infoState_3907_ = lean_ctor_get(v___x_3900_, 7);
v_snapshotTasks_3908_ = lean_ctor_get(v___x_3900_, 8);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v___x_3900_, 5);
lean_dec(v_unused_3938_);
v___x_3910_ = v___x_3900_;
v_isShared_3911_ = v_isSharedCheck_3937_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_snapshotTasks_3908_);
lean_inc(v_infoState_3907_);
lean_inc(v_messages_3906_);
lean_inc(v_traceState_3905_);
lean_inc(v_auxDeclNGen_3904_);
lean_inc(v_ngen_3903_);
lean_inc(v_nextMacroScope_3902_);
lean_inc(v_env_3901_);
lean_dec(v___x_3900_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3937_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
uint8_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3912_ = 0;
v___x_3913_ = lean_box(0);
v___x_3914_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_3901_, v_declName_3895_, v_s_3896_, v___x_3912_, v___x_3913_);
v___x_3915_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 5, v___x_3915_);
lean_ctor_set(v___x_3910_, 0, v___x_3914_);
v___x_3917_ = v___x_3910_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_nextMacroScope_3902_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_ngen_3903_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_auxDeclNGen_3904_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_traceState_3905_);
lean_ctor_set(v_reuseFailAlloc_3936_, 5, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3936_, 6, v_messages_3906_);
lean_ctor_set(v_reuseFailAlloc_3936_, 7, v_infoState_3907_);
lean_ctor_set(v_reuseFailAlloc_3936_, 8, v_snapshotTasks_3908_);
v___x_3917_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_mctx_3920_; lean_object* v_zetaDeltaFVarIds_3921_; lean_object* v_postponed_3922_; lean_object* v_diag_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3934_; 
v___x_3918_ = lean_st_ref_set(v___y_3898_, v___x_3917_);
v___x_3919_ = lean_st_ref_take(v___y_3897_);
v_mctx_3920_ = lean_ctor_get(v___x_3919_, 0);
v_zetaDeltaFVarIds_3921_ = lean_ctor_get(v___x_3919_, 2);
v_postponed_3922_ = lean_ctor_get(v___x_3919_, 3);
v_diag_3923_ = lean_ctor_get(v___x_3919_, 4);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3934_ == 0)
{
lean_object* v_unused_3935_; 
v_unused_3935_ = lean_ctor_get(v___x_3919_, 1);
lean_dec(v_unused_3935_);
v___x_3925_ = v___x_3919_;
v_isShared_3926_ = v_isSharedCheck_3934_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_diag_3923_);
lean_inc(v_postponed_3922_);
lean_inc(v_zetaDeltaFVarIds_3921_);
lean_inc(v_mctx_3920_);
lean_dec(v___x_3919_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3934_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 1, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_mctx_3920_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_zetaDeltaFVarIds_3921_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v_postponed_3922_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_diag_3923_);
v___x_3929_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3930_ = lean_st_ref_set(v___y_3897_, v___x_3929_);
v___x_3931_ = lean_box(0);
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
return v___x_3932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_3939_, lean_object* v_s_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
uint8_t v_s_boxed_3944_; lean_object* v_res_3945_; 
v_s_boxed_3944_ = lean_unbox(v_s_3940_);
v_res_3945_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3939_, v_s_boxed_3944_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_3946_, uint8_t v_s_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3946_, v_s_3947_, v___y_3949_, v___y_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_3954_, lean_object* v_s_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
uint8_t v_s_boxed_3961_; lean_object* v_res_3962_; 
v_s_boxed_3961_ = lean_unbox(v_s_3955_);
v_res_3962_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_3954_, v_s_boxed_3961_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_3963_, uint8_t v_attrKind_3964_, lean_object* v_prio_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3971_ = 3;
lean_inc(v_declName_3963_);
v___x_3972_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3963_, v___x_3971_, v_a_3967_, v_a_3969_);
lean_dec_ref(v___x_3972_);
v___x_3973_ = l_Lean_Meta_addInstance(v_declName_3963_, v_attrKind_3964_, v_prio_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_3974_, lean_object* v_attrKind_3975_, lean_object* v_prio_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
uint8_t v_attrKind_boxed_3982_; lean_object* v_res_3983_; 
v_attrKind_boxed_3982_ = lean_unbox(v_attrKind_3975_);
v_res_3983_ = l_Lean_Meta_registerInstance(v_declName_3974_, v_attrKind_boxed_3982_, v_prio_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_3984_, lean_object* v_x_3985_){
_start:
{
lean_inc_ref(v_a_3984_);
return v_a_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_3986_, lean_object* v_x_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_3986_, v_x_3987_);
lean_dec_ref(v_x_3987_);
lean_dec_ref(v_a_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; lean_object* v_env_3994_; lean_object* v_options_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3993_ = lean_st_ref_get(v___y_3991_);
v_env_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc_ref(v_env_3994_);
lean_dec(v___x_3993_);
v_options_3995_ = lean_ctor_get(v___y_3990_, 2);
v___x_3996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3997_ = lean_unsigned_to_nat(32u);
v___x_3998_ = lean_mk_empty_array_with_capacity(v___x_3997_);
lean_dec_ref(v___x_3998_);
v___x_3999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3995_);
v___x_4000_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4000_, 0, v_env_3994_);
lean_ctor_set(v___x_4000_, 1, v___x_3996_);
lean_ctor_set(v___x_4000_, 2, v___x_3999_);
lean_ctor_set(v___x_4000_, 3, v_options_3995_);
v___x_4001_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set(v___x_4001_, 1, v_msgData_3989_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_ref_4012_; lean_object* v___x_4013_; lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4022_; 
v_ref_4012_ = lean_ctor_get(v___y_4009_, 5);
v___x_4013_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4008_, v___y_4009_, v___y_4010_);
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4016_ = v___x_4013_;
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
lean_inc(v_ref_4012_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v_ref_4012_);
lean_ctor_set(v___x_4018_, 1, v_a_4014_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set_tag(v___x_4016_, 1);
lean_ctor_set(v___x_4016_, 0, v___x_4018_);
v___x_4020_ = v___x_4016_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4028_, lean_object* v_i_4029_, lean_object* v_k_4030_){
_start:
{
lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4031_ = lean_array_get_size(v_keys_4028_);
v___x_4032_ = lean_nat_dec_lt(v_i_4029_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_dec(v_i_4029_);
return v___x_4032_;
}
else
{
lean_object* v_k_x27_4033_; uint8_t v___x_4034_; 
v_k_x27_4033_ = lean_array_fget_borrowed(v_keys_4028_, v_i_4029_);
v___x_4034_ = lean_name_eq(v_k_4030_, v_k_x27_4033_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_unsigned_to_nat(1u);
v___x_4036_ = lean_nat_add(v_i_4029_, v___x_4035_);
lean_dec(v_i_4029_);
v_i_4029_ = v___x_4036_;
goto _start;
}
else
{
lean_dec(v_i_4029_);
return v___x_4034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4038_, lean_object* v_i_4039_, lean_object* v_k_4040_){
_start:
{
uint8_t v_res_4041_; lean_object* v_r_4042_; 
v_res_4041_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4038_, v_i_4039_, v_k_4040_);
lean_dec(v_k_4040_);
lean_dec_ref(v_keys_4038_);
v_r_4042_ = lean_box(v_res_4041_);
return v_r_4042_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4043_, size_t v_x_4044_, lean_object* v_x_4045_){
_start:
{
if (lean_obj_tag(v_x_4043_) == 0)
{
lean_object* v_es_4046_; lean_object* v___x_4047_; size_t v___x_4048_; size_t v___x_4049_; size_t v___x_4050_; lean_object* v_j_4051_; lean_object* v___x_4052_; 
v_es_4046_ = lean_ctor_get(v_x_4043_, 0);
v___x_4047_ = lean_box(2);
v___x_4048_ = ((size_t)5ULL);
v___x_4049_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4050_ = lean_usize_land(v_x_4044_, v___x_4049_);
v_j_4051_ = lean_usize_to_nat(v___x_4050_);
v___x_4052_ = lean_array_get_borrowed(v___x_4047_, v_es_4046_, v_j_4051_);
lean_dec(v_j_4051_);
switch(lean_obj_tag(v___x_4052_))
{
case 0:
{
lean_object* v_key_4053_; uint8_t v___x_4054_; 
v_key_4053_ = lean_ctor_get(v___x_4052_, 0);
v___x_4054_ = lean_name_eq(v_x_4045_, v_key_4053_);
return v___x_4054_;
}
case 1:
{
lean_object* v_node_4055_; size_t v___x_4056_; 
v_node_4055_ = lean_ctor_get(v___x_4052_, 0);
v___x_4056_ = lean_usize_shift_right(v_x_4044_, v___x_4048_);
v_x_4043_ = v_node_4055_;
v_x_4044_ = v___x_4056_;
goto _start;
}
default: 
{
uint8_t v___x_4058_; 
v___x_4058_ = 0;
return v___x_4058_;
}
}
}
else
{
lean_object* v_ks_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v_ks_4059_ = lean_ctor_get(v_x_4043_, 0);
v___x_4060_ = lean_unsigned_to_nat(0u);
v___x_4061_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4059_, v___x_4060_, v_x_4045_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4062_, lean_object* v_x_4063_, lean_object* v_x_4064_){
_start:
{
size_t v_x_2353__boxed_4065_; uint8_t v_res_4066_; lean_object* v_r_4067_; 
v_x_2353__boxed_4065_ = lean_unbox_usize(v_x_4063_);
lean_dec(v_x_4063_);
v_res_4066_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4062_, v_x_2353__boxed_4065_, v_x_4064_);
lean_dec(v_x_4064_);
lean_dec_ref(v_x_4062_);
v_r_4067_ = lean_box(v_res_4066_);
return v_r_4067_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4068_, lean_object* v_x_4069_){
_start:
{
uint64_t v___y_4071_; 
if (lean_obj_tag(v_x_4069_) == 0)
{
uint64_t v___x_4074_; 
v___x_4074_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4071_ = v___x_4074_;
goto v___jp_4070_;
}
else
{
uint64_t v_hash_4075_; 
v_hash_4075_ = lean_ctor_get_uint64(v_x_4069_, sizeof(void*)*2);
v___y_4071_ = v_hash_4075_;
goto v___jp_4070_;
}
v___jp_4070_:
{
size_t v___x_4072_; uint8_t v___x_4073_; 
v___x_4072_ = lean_uint64_to_usize(v___y_4071_);
v___x_4073_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4068_, v___x_4072_, v_x_4069_);
return v___x_4073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4076_, lean_object* v_x_4077_){
_start:
{
uint8_t v_res_4078_; lean_object* v_r_4079_; 
v_res_4078_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4076_, v_x_4077_);
lean_dec(v_x_4077_);
lean_dec_ref(v_x_4076_);
v_r_4079_ = lean_box(v_res_4078_);
return v_r_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4080_, lean_object* v_declName_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_instanceNames_4088_; uint8_t v___x_4089_; 
v_instanceNames_4088_ = lean_ctor_get(v_d_4080_, 1);
v___x_4089_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4088_, v_declName_4081_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec_ref(v_d_4080_);
v___x_4090_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4091_ = l_Lean_MessageData_ofConstName(v_declName_4081_, v___x_4089_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4094_, v___y_4082_, v___y_4083_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
else
{
goto v___jp_4085_;
}
v___jp_4085_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = l_Lean_Meta_Instances_eraseCore(v_d_4080_, v_declName_4081_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4104_, lean_object* v_declName_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4104_, v_declName_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4110_, lean_object* v_declName_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v___x_4117_; lean_object* v_ext_4118_; lean_object* v_toEnvExtension_4119_; lean_object* v_asyncMode_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4115_ = lean_st_ref_get(v___y_4113_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_ref(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4117_ = l_Lean_Meta_instanceExtension;
v_ext_4118_ = lean_ctor_get(v___x_4117_, 1);
v_toEnvExtension_4119_ = lean_ctor_get(v_ext_4118_, 0);
v_asyncMode_4120_ = lean_ctor_get(v_toEnvExtension_4119_, 2);
v___x_4121_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4110_, v___x_4117_, v_env_4116_, v_asyncMode_4120_);
v___x_4122_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4121_, v_declName_4111_, v___y_4112_, v___y_4113_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4152_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4152_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4152_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v_env_4128_; lean_object* v_nextMacroScope_4129_; lean_object* v_ngen_4130_; lean_object* v_auxDeclNGen_4131_; lean_object* v_traceState_4132_; lean_object* v_messages_4133_; lean_object* v_infoState_4134_; lean_object* v_snapshotTasks_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4150_; 
v___x_4127_ = lean_st_ref_take(v___y_4113_);
v_env_4128_ = lean_ctor_get(v___x_4127_, 0);
v_nextMacroScope_4129_ = lean_ctor_get(v___x_4127_, 1);
v_ngen_4130_ = lean_ctor_get(v___x_4127_, 2);
v_auxDeclNGen_4131_ = lean_ctor_get(v___x_4127_, 3);
v_traceState_4132_ = lean_ctor_get(v___x_4127_, 4);
v_messages_4133_ = lean_ctor_get(v___x_4127_, 6);
v_infoState_4134_ = lean_ctor_get(v___x_4127_, 7);
v_snapshotTasks_4135_ = lean_ctor_get(v___x_4127_, 8);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v___x_4127_, 5);
lean_dec(v_unused_4151_);
v___x_4137_ = v___x_4127_;
v_isShared_4138_ = v_isSharedCheck_4150_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_snapshotTasks_4135_);
lean_inc(v_infoState_4134_);
lean_inc(v_messages_4133_);
lean_inc(v_traceState_4132_);
lean_inc(v_auxDeclNGen_4131_);
lean_inc(v_ngen_4130_);
lean_inc(v_nextMacroScope_4129_);
lean_inc(v_env_4128_);
lean_dec(v___x_4127_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4150_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___f_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___f_4139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4139_, 0, v_a_4123_);
v___x_4140_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4117_, v_env_4128_, v___f_4139_);
v___x_4141_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 5, v___x_4141_);
lean_ctor_set(v___x_4137_, 0, v___x_4140_);
v___x_4143_ = v___x_4137_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4140_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v_nextMacroScope_4129_);
lean_ctor_set(v_reuseFailAlloc_4149_, 2, v_ngen_4130_);
lean_ctor_set(v_reuseFailAlloc_4149_, 3, v_auxDeclNGen_4131_);
lean_ctor_set(v_reuseFailAlloc_4149_, 4, v_traceState_4132_);
lean_ctor_set(v_reuseFailAlloc_4149_, 5, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4149_, 6, v_messages_4133_);
lean_ctor_set(v_reuseFailAlloc_4149_, 7, v_infoState_4134_);
lean_ctor_set(v_reuseFailAlloc_4149_, 8, v_snapshotTasks_4135_);
v___x_4143_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4144_ = lean_st_ref_set(v___y_4113_, v___x_4143_);
v___x_4145_ = lean_box(0);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4145_);
v___x_4147_ = v___x_4125_;
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
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
v_a_4153_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4122_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4122_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4161_, lean_object* v_declName_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4161_, v_declName_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v___x_4161_);
return v_res_4166_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4173_; uint64_t v___x_4174_; 
v___x_4173_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4174_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4173_);
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4175_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4176_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set_uint64(v___x_4177_, sizeof(void*)*1, v___x_4175_);
return v___x_4177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4182_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
lean_ctor_set(v___x_4182_, 2, v___x_4181_);
lean_ctor_set(v___x_4182_, 3, v___x_4181_);
lean_ctor_set(v___x_4182_, 4, v___x_4181_);
lean_ctor_set(v___x_4182_, 5, v___x_4181_);
return v___x_4182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
lean_ctor_set(v___x_4184_, 2, v___x_4183_);
lean_ctor_set(v___x_4184_, 3, v___x_4183_);
lean_ctor_set(v___x_4184_, 4, v___x_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v_declName_4187_, lean_object* v_stx_4188_, uint8_t v_attrKind_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = lean_unsigned_to_nat(1u);
v___x_4194_ = l_Lean_Syntax_getArg(v_stx_4188_, v___x_4193_);
v___x_4195_ = l_Lean_getAttrParamOptPrio(v___x_4194_, v___y_4190_, v___y_4191_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; uint8_t v___x_4197_; uint8_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; size_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4195_);
v___x_4197_ = 0;
v___x_4198_ = 1;
v___x_4199_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4200_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4201_ = lean_unsigned_to_nat(32u);
v___x_4202_ = lean_mk_empty_array_with_capacity(v___x_4201_);
v___x_4203_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4204_ = ((size_t)5ULL);
lean_inc_n(v___x_4185_, 6);
v___x_4205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v___x_4202_);
lean_ctor_set(v___x_4205_, 2, v___x_4185_);
lean_ctor_set(v___x_4205_, 3, v___x_4185_);
lean_ctor_set_usize(v___x_4205_, 4, v___x_4204_);
v___x_4206_ = lean_box(1);
lean_inc_ref(v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4200_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
lean_ctor_set(v___x_4207_, 2, v___x_4206_);
v___x_4208_ = lean_mk_empty_array_with_capacity(v___x_4185_);
v___x_4209_ = lean_box(0);
lean_inc(v___x_4186_);
v___x_4210_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4210_, 0, v___x_4199_);
lean_ctor_set(v___x_4210_, 1, v___x_4186_);
lean_ctor_set(v___x_4210_, 2, v___x_4207_);
lean_ctor_set(v___x_4210_, 3, v___x_4208_);
lean_ctor_set(v___x_4210_, 4, v___x_4209_);
lean_ctor_set(v___x_4210_, 5, v___x_4185_);
lean_ctor_set(v___x_4210_, 6, v___x_4209_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*7, v___x_4197_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*7 + 1, v___x_4197_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*7 + 2, v___x_4197_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*7 + 3, v___x_4198_);
v___x_4211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4185_);
lean_ctor_set(v___x_4211_, 1, v___x_4185_);
lean_ctor_set(v___x_4211_, 2, v___x_4185_);
lean_ctor_set(v___x_4211_, 3, v___x_4185_);
lean_ctor_set(v___x_4211_, 4, v___x_4200_);
lean_ctor_set(v___x_4211_, 5, v___x_4200_);
lean_ctor_set(v___x_4211_, 6, v___x_4200_);
lean_ctor_set(v___x_4211_, 7, v___x_4200_);
lean_ctor_set(v___x_4211_, 8, v___x_4200_);
lean_ctor_set(v___x_4211_, 9, v___x_4200_);
v___x_4212_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4213_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4211_);
lean_ctor_set(v___x_4214_, 1, v___x_4212_);
lean_ctor_set(v___x_4214_, 2, v___x_4186_);
lean_ctor_set(v___x_4214_, 3, v___x_4205_);
lean_ctor_set(v___x_4214_, 4, v___x_4213_);
v___x_4215_ = lean_st_mk_ref(v___x_4214_);
v___x_4216_ = l_Lean_Meta_addInstance(v_declName_4187_, v_attrKind_4189_, v_a_4196_, v___x_4210_, v___x_4215_, v___y_4190_, v___y_4191_);
lean_dec_ref(v___x_4210_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4225_; 
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v___x_4216_, 0);
lean_dec(v_unused_4226_);
v___x_4218_ = v___x_4216_;
v_isShared_4219_ = v_isSharedCheck_4225_;
goto v_resetjp_4217_;
}
else
{
lean_dec(v___x_4216_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4225_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
v___x_4220_ = lean_st_ref_get(v___x_4215_);
lean_dec(v___x_4215_);
lean_dec(v___x_4220_);
v___x_4221_ = lean_box(0);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___x_4221_);
v___x_4223_ = v___x_4218_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_dec(v___x_4215_);
return v___x_4216_;
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_declName_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
v_a_4227_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4195_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4195_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4235_, lean_object* v___x_4236_, lean_object* v_declName_4237_, lean_object* v_stx_4238_, lean_object* v_attrKind_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
uint8_t v_attrKind_boxed_4243_; lean_object* v_res_4244_; 
v_attrKind_boxed_4243_ = lean_unbox(v_attrKind_4239_);
v_res_4244_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4235_, v___x_4236_, v_declName_4237_, v_stx_4238_, v_attrKind_boxed_4243_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v_stx_4238_);
return v_res_4244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4245_; lean_object* v___f_4246_; 
v___x_4245_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4246_, 0, v___x_4245_);
return v___f_4246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___f_4313_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4314_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v___f_4314_);
lean_ctor_set(v___x_4316_, 2, v___f_4313_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4319_ = l_Lean_registerBuiltinAttribute(v___x_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4321_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4322_, lean_object* v_x_4323_, lean_object* v_x_4324_){
_start:
{
uint8_t v___x_4325_; 
v___x_4325_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4323_, v_x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4326_, lean_object* v_x_4327_, lean_object* v_x_4328_){
_start:
{
uint8_t v_res_4329_; lean_object* v_r_4330_; 
v_res_4329_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4326_, v_x_4327_, v_x_4328_);
lean_dec(v_x_4328_);
lean_dec_ref(v_x_4327_);
v_r_4330_ = lean_box(v_res_4329_);
return v_r_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4331_, lean_object* v_msg_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4332_, v___y_4333_, v___y_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4337_, lean_object* v_msg_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4337_, v_msg_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
return v_res_4342_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4343_, lean_object* v_x_4344_, size_t v_x_4345_, lean_object* v_x_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4344_, v_x_4345_, v_x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4348_, lean_object* v_x_4349_, lean_object* v_x_4350_, lean_object* v_x_4351_){
_start:
{
size_t v_x_3005__boxed_4352_; uint8_t v_res_4353_; lean_object* v_r_4354_; 
v_x_3005__boxed_4352_ = lean_unbox_usize(v_x_4350_);
lean_dec(v_x_4350_);
v_res_4353_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4348_, v_x_4349_, v_x_3005__boxed_4352_, v_x_4351_);
lean_dec(v_x_4351_);
lean_dec_ref(v_x_4349_);
v_r_4354_ = lean_box(v_res_4353_);
return v_r_4354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4355_, lean_object* v_keys_4356_, lean_object* v_vals_4357_, lean_object* v_heq_4358_, lean_object* v_i_4359_, lean_object* v_k_4360_){
_start:
{
uint8_t v___x_4361_; 
v___x_4361_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4356_, v_i_4359_, v_k_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4362_, lean_object* v_keys_4363_, lean_object* v_vals_4364_, lean_object* v_heq_4365_, lean_object* v_i_4366_, lean_object* v_k_4367_){
_start:
{
uint8_t v_res_4368_; lean_object* v_r_4369_; 
v_res_4368_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4362_, v_keys_4363_, v_vals_4364_, v_heq_4365_, v_i_4366_, v_k_4367_);
lean_dec(v_k_4367_);
lean_dec_ref(v_vals_4364_);
lean_dec_ref(v_keys_4363_);
v_r_4369_ = lean_box(v_res_4368_);
return v_r_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4373_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4374_ = l_Lean_addBuiltinDocString(v___x_4372_, v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4377_){
_start:
{
lean_object* v___x_4379_; lean_object* v_env_4380_; lean_object* v___x_4381_; lean_object* v_ext_4382_; lean_object* v_toEnvExtension_4383_; lean_object* v_asyncMode_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v_discrTree_4387_; lean_object* v___x_4388_; 
v___x_4379_ = lean_st_ref_get(v_a_4377_);
v_env_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc_ref(v_env_4380_);
lean_dec(v___x_4379_);
v___x_4381_ = l_Lean_Meta_instanceExtension;
v_ext_4382_ = lean_ctor_get(v___x_4381_, 1);
v_toEnvExtension_4383_ = lean_ctor_get(v_ext_4382_, 0);
v_asyncMode_4384_ = lean_ctor_get(v_toEnvExtension_4383_, 2);
v___x_4385_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4386_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4385_, v___x_4381_, v_env_4380_, v_asyncMode_4384_);
v_discrTree_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc_ref(v_discrTree_4387_);
lean_dec(v___x_4386_);
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v_discrTree_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4389_);
lean_dec(v_a_4389_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4393_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4396_, v_a_4397_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v_env_4403_; lean_object* v___x_4404_; lean_object* v_ext_4405_; lean_object* v_toEnvExtension_4406_; lean_object* v_asyncMode_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v_erased_4410_; lean_object* v___x_4411_; 
v___x_4402_ = lean_st_ref_get(v_a_4400_);
v_env_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc_ref(v_env_4403_);
lean_dec(v___x_4402_);
v___x_4404_ = l_Lean_Meta_instanceExtension;
v_ext_4405_ = lean_ctor_get(v___x_4404_, 1);
v_toEnvExtension_4406_ = lean_ctor_get(v_ext_4405_, 0);
v_asyncMode_4407_ = lean_ctor_get(v_toEnvExtension_4406_, 2);
v___x_4408_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4409_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4408_, v___x_4404_, v_env_4403_, v_asyncMode_4407_);
v_erased_4410_ = lean_ctor_get(v___x_4409_, 2);
lean_inc_ref(v_erased_4410_);
lean_dec(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v_erased_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4412_);
lean_dec(v_a_4412_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Meta_getErasedInstances(v_a_4419_, v_a_4420_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
return v_res_4422_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4423_, lean_object* v_declName_4424_){
_start:
{
lean_object* v___x_4425_; lean_object* v_ext_4426_; lean_object* v_toEnvExtension_4427_; lean_object* v_asyncMode_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v_instanceNames_4431_; uint8_t v___x_4432_; 
v___x_4425_ = l_Lean_Meta_instanceExtension;
v_ext_4426_ = lean_ctor_get(v___x_4425_, 1);
v_toEnvExtension_4427_ = lean_ctor_get(v_ext_4426_, 0);
v_asyncMode_4428_ = lean_ctor_get(v_toEnvExtension_4427_, 2);
v___x_4429_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4430_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4429_, v___x_4425_, v_env_4423_, v_asyncMode_4428_);
v_instanceNames_4431_ = lean_ctor_get(v___x_4430_, 1);
lean_inc_ref(v_instanceNames_4431_);
lean_dec(v___x_4430_);
v___x_4432_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4431_, v_declName_4424_);
lean_dec_ref(v_instanceNames_4431_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4433_, lean_object* v_declName_4434_){
_start:
{
uint8_t v_res_4435_; lean_object* v_r_4436_; 
v_res_4435_ = l_Lean_Meta_isInstanceCore(v_env_4433_, v_declName_4434_);
lean_dec(v_declName_4434_);
v_r_4436_ = lean_box(v_res_4435_);
return v_r_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___x_4440_; lean_object* v_env_4441_; uint8_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4440_ = lean_st_ref_get(v_a_4438_);
v_env_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc_ref(v_env_4441_);
lean_dec(v___x_4440_);
v___x_4442_ = l_Lean_Meta_isInstanceCore(v_env_4441_, v_declName_4437_);
v___x_4443_ = lean_box(v___x_4442_);
v___x_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Meta_isInstance___redArg(v_declName_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec(v_declName_4445_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_Meta_isInstance___redArg(v_declName_4449_, v_a_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_Meta_isInstance(v_declName_4454_, v_a_4455_, v_a_4456_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_declName_4454_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4459_, lean_object* v_vals_4460_, lean_object* v_i_4461_, lean_object* v_k_4462_){
_start:
{
lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4463_ = lean_array_get_size(v_keys_4459_);
v___x_4464_ = lean_nat_dec_lt(v_i_4461_, v___x_4463_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; 
lean_dec(v_i_4461_);
v___x_4465_ = lean_box(0);
return v___x_4465_;
}
else
{
lean_object* v_k_x27_4466_; uint8_t v___x_4467_; 
v_k_x27_4466_ = lean_array_fget_borrowed(v_keys_4459_, v_i_4461_);
v___x_4467_ = lean_name_eq(v_k_4462_, v_k_x27_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = lean_unsigned_to_nat(1u);
v___x_4469_ = lean_nat_add(v_i_4461_, v___x_4468_);
lean_dec(v_i_4461_);
v_i_4461_ = v___x_4469_;
goto _start;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = lean_array_fget_borrowed(v_vals_4460_, v_i_4461_);
lean_dec(v_i_4461_);
lean_inc(v___x_4471_);
v___x_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4473_, lean_object* v_vals_4474_, lean_object* v_i_4475_, lean_object* v_k_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4473_, v_vals_4474_, v_i_4475_, v_k_4476_);
lean_dec(v_k_4476_);
lean_dec_ref(v_vals_4474_);
lean_dec_ref(v_keys_4473_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4478_, size_t v_x_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v_es_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4502_; 
v_es_4481_ = lean_ctor_get(v_x_4478_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4483_ = v_x_4478_;
v_isShared_4484_ = v_isSharedCheck_4502_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_es_4481_);
lean_dec(v_x_4478_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4502_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; size_t v___x_4486_; size_t v___x_4487_; size_t v___x_4488_; lean_object* v_j_4489_; lean_object* v___x_4490_; 
v___x_4485_ = lean_box(2);
v___x_4486_ = ((size_t)5ULL);
v___x_4487_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4488_ = lean_usize_land(v_x_4479_, v___x_4487_);
v_j_4489_ = lean_usize_to_nat(v___x_4488_);
v___x_4490_ = lean_array_get(v___x_4485_, v_es_4481_, v_j_4489_);
lean_dec(v_j_4489_);
lean_dec_ref(v_es_4481_);
switch(lean_obj_tag(v___x_4490_))
{
case 0:
{
lean_object* v_key_4491_; lean_object* v_val_4492_; uint8_t v___x_4493_; 
v_key_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_key_4491_);
v_val_4492_ = lean_ctor_get(v___x_4490_, 1);
lean_inc(v_val_4492_);
lean_dec_ref(v___x_4490_);
v___x_4493_ = lean_name_eq(v_x_4480_, v_key_4491_);
lean_dec(v_key_4491_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
lean_dec(v_val_4492_);
lean_del_object(v___x_4483_);
v___x_4494_ = lean_box(0);
return v___x_4494_;
}
else
{
lean_object* v___x_4496_; 
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 1);
lean_ctor_set(v___x_4483_, 0, v_val_4492_);
v___x_4496_ = v___x_4483_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_val_4492_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
case 1:
{
lean_object* v_node_4498_; size_t v___x_4499_; 
lean_del_object(v___x_4483_);
v_node_4498_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_node_4498_);
lean_dec_ref(v___x_4490_);
v___x_4499_ = lean_usize_shift_right(v_x_4479_, v___x_4486_);
v_x_4478_ = v_node_4498_;
v_x_4479_ = v___x_4499_;
goto _start;
}
default: 
{
lean_object* v___x_4501_; 
lean_del_object(v___x_4483_);
v___x_4501_ = lean_box(0);
return v___x_4501_;
}
}
}
}
else
{
lean_object* v_ks_4503_; lean_object* v_vs_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v_ks_4503_ = lean_ctor_get(v_x_4478_, 0);
lean_inc_ref(v_ks_4503_);
v_vs_4504_ = lean_ctor_get(v_x_4478_, 1);
lean_inc_ref(v_vs_4504_);
lean_dec_ref(v_x_4478_);
v___x_4505_ = lean_unsigned_to_nat(0u);
v___x_4506_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4503_, v_vs_4504_, v___x_4505_, v_x_4480_);
lean_dec_ref(v_vs_4504_);
lean_dec_ref(v_ks_4503_);
return v___x_4506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4507_, lean_object* v_x_4508_, lean_object* v_x_4509_){
_start:
{
size_t v_x_489__boxed_4510_; lean_object* v_res_4511_; 
v_x_489__boxed_4510_ = lean_unbox_usize(v_x_4508_);
lean_dec(v_x_4508_);
v_res_4511_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4507_, v_x_489__boxed_4510_, v_x_4509_);
lean_dec(v_x_4509_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4512_, lean_object* v_x_4513_){
_start:
{
uint64_t v___y_4515_; 
if (lean_obj_tag(v_x_4513_) == 0)
{
uint64_t v___x_4518_; 
v___x_4518_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4515_ = v___x_4518_;
goto v___jp_4514_;
}
else
{
uint64_t v_hash_4519_; 
v_hash_4519_ = lean_ctor_get_uint64(v_x_4513_, sizeof(void*)*2);
v___y_4515_ = v_hash_4519_;
goto v___jp_4514_;
}
v___jp_4514_:
{
size_t v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_uint64_to_usize(v___y_4515_);
v___x_4517_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4512_, v___x_4516_, v_x_4513_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4520_, lean_object* v_x_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4520_, v_x_4521_);
lean_dec(v_x_4521_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v___x_4526_; lean_object* v_env_4527_; lean_object* v___x_4528_; lean_object* v_ext_4529_; lean_object* v_toEnvExtension_4530_; lean_object* v_asyncMode_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v_instanceNames_4534_; lean_object* v___x_4535_; 
v___x_4526_ = lean_st_ref_get(v_a_4524_);
v_env_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc_ref(v_env_4527_);
lean_dec(v___x_4526_);
v___x_4528_ = l_Lean_Meta_instanceExtension;
v_ext_4529_ = lean_ctor_get(v___x_4528_, 1);
v_toEnvExtension_4530_ = lean_ctor_get(v_ext_4529_, 0);
v_asyncMode_4531_ = lean_ctor_get(v_toEnvExtension_4530_, 2);
v___x_4532_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4533_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4532_, v___x_4528_, v_env_4527_, v_asyncMode_4531_);
v_instanceNames_4534_ = lean_ctor_get(v___x_4533_, 1);
lean_inc_ref(v_instanceNames_4534_);
lean_dec(v___x_4533_);
v___x_4535_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4534_, v_declName_4523_);
if (lean_obj_tag(v___x_4535_) == 1)
{
lean_object* v_val_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4545_; 
v_val_4536_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4538_ = v___x_4535_;
v_isShared_4539_ = v_isSharedCheck_4545_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_val_4536_);
lean_dec(v___x_4535_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4545_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v_priority_4540_; lean_object* v___x_4542_; 
v_priority_4540_ = lean_ctor_get(v_val_4536_, 2);
lean_inc(v_priority_4540_);
lean_dec(v_val_4536_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v_priority_4540_);
v___x_4542_ = v___x_4538_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_priority_4540_);
v___x_4542_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec(v___x_4535_);
v___x_4546_ = lean_box(0);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec(v_declName_4548_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4552_, v_a_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4557_, v_a_4558_, v_a_4559_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_declName_4557_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4562_, lean_object* v_x_4563_, lean_object* v_x_4564_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4563_, v_x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4566_, lean_object* v_x_4567_, lean_object* v_x_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4566_, v_x_4567_, v_x_4568_);
lean_dec(v_x_4568_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4570_, lean_object* v_x_4571_, size_t v_x_4572_, lean_object* v_x_4573_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4571_, v_x_4572_, v_x_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4575_, lean_object* v_x_4576_, lean_object* v_x_4577_, lean_object* v_x_4578_){
_start:
{
size_t v_x_617__boxed_4579_; lean_object* v_res_4580_; 
v_x_617__boxed_4579_ = lean_unbox_usize(v_x_4577_);
lean_dec(v_x_4577_);
v_res_4580_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4575_, v_x_4576_, v_x_617__boxed_4579_, v_x_4578_);
lean_dec(v_x_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4581_, lean_object* v_keys_4582_, lean_object* v_vals_4583_, lean_object* v_heq_4584_, lean_object* v_i_4585_, lean_object* v_k_4586_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4582_, v_vals_4583_, v_i_4585_, v_k_4586_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4588_, lean_object* v_keys_4589_, lean_object* v_vals_4590_, lean_object* v_heq_4591_, lean_object* v_i_4592_, lean_object* v_k_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4588_, v_keys_4589_, v_vals_4590_, v_heq_4591_, v_i_4592_, v_k_4593_);
lean_dec(v_k_4593_);
lean_dec_ref(v_vals_4590_);
lean_dec_ref(v_keys_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___x_4598_; lean_object* v_env_4599_; lean_object* v___x_4600_; lean_object* v_ext_4601_; lean_object* v_toEnvExtension_4602_; lean_object* v_asyncMode_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v_instanceNames_4606_; lean_object* v___x_4607_; 
v___x_4598_ = lean_st_ref_get(v_a_4596_);
v_env_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc_ref(v_env_4599_);
lean_dec(v___x_4598_);
v___x_4600_ = l_Lean_Meta_instanceExtension;
v_ext_4601_ = lean_ctor_get(v___x_4600_, 1);
v_toEnvExtension_4602_ = lean_ctor_get(v_ext_4601_, 0);
v_asyncMode_4603_ = lean_ctor_get(v_toEnvExtension_4602_, 2);
v___x_4604_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4605_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4604_, v___x_4600_, v_env_4599_, v_asyncMode_4603_);
v_instanceNames_4606_ = lean_ctor_get(v___x_4605_, 1);
lean_inc_ref(v_instanceNames_4606_);
lean_dec(v___x_4605_);
v___x_4607_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4606_, v_declName_4595_);
if (lean_obj_tag(v___x_4607_) == 1)
{
lean_object* v_val_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4618_; 
v_val_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4618_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_val_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4618_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
uint8_t v_attrKind_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
v_attrKind_4612_ = lean_ctor_get_uint8(v_val_4608_, sizeof(void*)*5);
lean_dec(v_val_4608_);
v___x_4613_ = lean_box(v_attrKind_4612_);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4613_);
v___x_4615_ = v___x_4610_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4613_);
v___x_4615_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_dec(v___x_4607_);
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4621_, v_a_4622_);
lean_dec(v_a_4622_);
lean_dec(v_declName_4621_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4625_, v_a_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_declName_4630_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_4639_, lean_object* v_v_4640_, lean_object* v_t_4641_){
_start:
{
if (lean_obj_tag(v_t_4641_) == 0)
{
lean_object* v_size_4642_; lean_object* v_k_4643_; lean_object* v_v_4644_; lean_object* v_l_4645_; lean_object* v_r_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4927_; 
v_size_4642_ = lean_ctor_get(v_t_4641_, 0);
v_k_4643_ = lean_ctor_get(v_t_4641_, 1);
v_v_4644_ = lean_ctor_get(v_t_4641_, 2);
v_l_4645_ = lean_ctor_get(v_t_4641_, 3);
v_r_4646_ = lean_ctor_get(v_t_4641_, 4);
v_isSharedCheck_4927_ = !lean_is_exclusive(v_t_4641_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4648_ = v_t_4641_;
v_isShared_4649_ = v_isSharedCheck_4927_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_r_4646_);
lean_inc(v_l_4645_);
lean_inc(v_v_4644_);
lean_inc(v_k_4643_);
lean_inc(v_size_4642_);
lean_dec(v_t_4641_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4927_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_nat_dec_lt(v_k_4643_, v_k_4639_);
if (v___x_4650_ == 0)
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_nat_dec_eq(v_k_4643_, v_k_4639_);
if (v___x_4651_ == 0)
{
lean_object* v_impl_4652_; lean_object* v___x_4653_; 
lean_dec(v_size_4642_);
v_impl_4652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4639_, v_v_4640_, v_r_4646_);
v___x_4653_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4645_) == 0)
{
lean_object* v_size_4654_; lean_object* v_size_4655_; lean_object* v_k_4656_; lean_object* v_v_4657_; lean_object* v_l_4658_; lean_object* v_r_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v_size_4654_ = lean_ctor_get(v_l_4645_, 0);
v_size_4655_ = lean_ctor_get(v_impl_4652_, 0);
lean_inc(v_size_4655_);
v_k_4656_ = lean_ctor_get(v_impl_4652_, 1);
lean_inc(v_k_4656_);
v_v_4657_ = lean_ctor_get(v_impl_4652_, 2);
lean_inc(v_v_4657_);
v_l_4658_ = lean_ctor_get(v_impl_4652_, 3);
lean_inc(v_l_4658_);
v_r_4659_ = lean_ctor_get(v_impl_4652_, 4);
lean_inc(v_r_4659_);
v___x_4660_ = lean_unsigned_to_nat(3u);
v___x_4661_ = lean_nat_mul(v___x_4660_, v_size_4654_);
v___x_4662_ = lean_nat_dec_lt(v___x_4661_, v_size_4655_);
lean_dec(v___x_4661_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
lean_dec(v_r_4659_);
lean_dec(v_l_4658_);
lean_dec(v_v_4657_);
lean_dec(v_k_4656_);
v___x_4663_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4664_ = lean_nat_add(v___x_4663_, v_size_4655_);
lean_dec(v_size_4655_);
lean_dec(v___x_4663_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_impl_4652_);
lean_ctor_set(v___x_4648_, 0, v___x_4664_);
v___x_4666_ = v___x_4648_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4667_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4667_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4667_, 4, v_impl_4652_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
else
{
lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4731_; 
v_isSharedCheck_4731_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; 
v_unused_4732_ = lean_ctor_get(v_impl_4652_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_impl_4652_, 2);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_impl_4652_, 1);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4736_);
v___x_4669_ = v_impl_4652_;
v_isShared_4670_ = v_isSharedCheck_4731_;
goto v_resetjp_4668_;
}
else
{
lean_dec(v_impl_4652_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4731_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v_size_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v_l_4674_; lean_object* v_r_4675_; lean_object* v_size_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v_size_4671_ = lean_ctor_get(v_l_4658_, 0);
v_k_4672_ = lean_ctor_get(v_l_4658_, 1);
v_v_4673_ = lean_ctor_get(v_l_4658_, 2);
v_l_4674_ = lean_ctor_get(v_l_4658_, 3);
v_r_4675_ = lean_ctor_get(v_l_4658_, 4);
v_size_4676_ = lean_ctor_get(v_r_4659_, 0);
v___x_4677_ = lean_unsigned_to_nat(2u);
v___x_4678_ = lean_nat_mul(v___x_4677_, v_size_4676_);
v___x_4679_ = lean_nat_dec_lt(v_size_4671_, v___x_4678_);
lean_dec(v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4707_; 
lean_inc(v_r_4675_);
lean_inc(v_l_4674_);
lean_inc(v_v_4673_);
lean_inc(v_k_4672_);
v_isSharedCheck_4707_ = !lean_is_exclusive(v_l_4658_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; lean_object* v_unused_4712_; 
v_unused_4708_ = lean_ctor_get(v_l_4658_, 4);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_l_4658_, 3);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_l_4658_, 2);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_l_4658_, 1);
lean_dec(v_unused_4711_);
v_unused_4712_ = lean_ctor_get(v_l_4658_, 0);
lean_dec(v_unused_4712_);
v___x_4681_ = v_l_4658_;
v_isShared_4682_ = v_isSharedCheck_4707_;
goto v_resetjp_4680_;
}
else
{
lean_dec(v_l_4658_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4707_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4697_; 
v___x_4683_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4684_ = lean_nat_add(v___x_4683_, v_size_4655_);
lean_dec(v_size_4655_);
if (lean_obj_tag(v_l_4674_) == 0)
{
lean_object* v_size_4705_; 
v_size_4705_ = lean_ctor_get(v_l_4674_, 0);
lean_inc(v_size_4705_);
v___y_4697_ = v_size_4705_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_unsigned_to_nat(0u);
v___y_4697_ = v___x_4706_;
goto v___jp_4696_;
}
v___jp_4685_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4689_ = lean_nat_add(v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec(v___y_4687_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 4, v_r_4659_);
lean_ctor_set(v___x_4681_, 3, v_r_4675_);
lean_ctor_set(v___x_4681_, 2, v_v_4657_);
lean_ctor_set(v___x_4681_, 1, v_k_4656_);
lean_ctor_set(v___x_4681_, 0, v___x_4689_);
v___x_4691_ = v___x_4681_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_k_4656_);
lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_v_4657_);
lean_ctor_set(v_reuseFailAlloc_4695_, 3, v_r_4675_);
lean_ctor_set(v_reuseFailAlloc_4695_, 4, v_r_4659_);
v___x_4691_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4693_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 4, v___x_4691_);
lean_ctor_set(v___x_4669_, 3, v___y_4686_);
lean_ctor_set(v___x_4669_, 2, v_v_4673_);
lean_ctor_set(v___x_4669_, 1, v_k_4672_);
lean_ctor_set(v___x_4669_, 0, v___x_4684_);
v___x_4693_ = v___x_4669_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4684_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v___y_4686_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
v___jp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4698_ = lean_nat_add(v___x_4683_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec(v___x_4683_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_l_4674_);
lean_ctor_set(v___x_4648_, 0, v___x_4698_);
v___x_4700_ = v___x_4648_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4704_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4704_, 4, v_l_4674_);
v___x_4700_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_nat_add(v___x_4653_, v_size_4676_);
if (lean_obj_tag(v_r_4675_) == 0)
{
lean_object* v_size_4702_; 
v_size_4702_ = lean_ctor_get(v_r_4675_, 0);
lean_inc(v_size_4702_);
v___y_4686_ = v___x_4700_;
v___y_4687_ = v___x_4701_;
v___y_4688_ = v_size_4702_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_unsigned_to_nat(0u);
v___y_4686_ = v___x_4700_;
v___y_4687_ = v___x_4701_;
v___y_4688_ = v___x_4703_;
goto v___jp_4685_;
}
}
}
}
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
lean_del_object(v___x_4648_);
v___x_4713_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4714_ = lean_nat_add(v___x_4713_, v_size_4655_);
lean_dec(v_size_4655_);
v___x_4715_ = lean_nat_add(v___x_4713_, v_size_4671_);
lean_dec(v___x_4713_);
lean_inc_ref(v_l_4645_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 4, v_l_4658_);
lean_ctor_set(v___x_4669_, 3, v_l_4645_);
lean_ctor_set(v___x_4669_, 2, v_v_4644_);
lean_ctor_set(v___x_4669_, 1, v_k_4643_);
lean_ctor_set(v___x_4669_, 0, v___x_4715_);
v___x_4717_ = v___x_4669_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_l_4658_);
v___x_4717_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
v_isSharedCheck_4724_ = !lean_is_exclusive(v_l_4645_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4725_ = lean_ctor_get(v_l_4645_, 4);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_l_4645_, 3);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_l_4645_, 2);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_l_4645_, 1);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_l_4645_, 0);
lean_dec(v_unused_4729_);
v___x_4719_ = v_l_4645_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_dec(v_l_4645_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 4, v_r_4659_);
lean_ctor_set(v___x_4719_, 3, v___x_4717_);
lean_ctor_set(v___x_4719_, 2, v_v_4657_);
lean_ctor_set(v___x_4719_, 1, v_k_4656_);
lean_ctor_set(v___x_4719_, 0, v___x_4714_);
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4656_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4657_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_r_4659_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4737_; 
v_l_4737_ = lean_ctor_get(v_impl_4652_, 3);
lean_inc(v_l_4737_);
if (lean_obj_tag(v_l_4737_) == 0)
{
lean_object* v_r_4738_; lean_object* v_k_4739_; lean_object* v_v_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4763_; 
v_r_4738_ = lean_ctor_get(v_impl_4652_, 4);
v_k_4739_ = lean_ctor_get(v_impl_4652_, 1);
v_v_4740_ = lean_ctor_get(v_impl_4652_, 2);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; lean_object* v_unused_4765_; 
v_unused_4764_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4764_);
v_unused_4765_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4765_);
v___x_4742_ = v_impl_4652_;
v_isShared_4743_ = v_isSharedCheck_4763_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_r_4738_);
lean_inc(v_v_4740_);
lean_inc(v_k_4739_);
lean_dec(v_impl_4652_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4763_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_k_4744_; lean_object* v_v_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4759_; 
v_k_4744_ = lean_ctor_get(v_l_4737_, 1);
v_v_4745_ = lean_ctor_get(v_l_4737_, 2);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_l_4737_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; lean_object* v_unused_4761_; lean_object* v_unused_4762_; 
v_unused_4760_ = lean_ctor_get(v_l_4737_, 4);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_l_4737_, 3);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v_l_4737_, 0);
lean_dec(v_unused_4762_);
v___x_4747_ = v_l_4737_;
v_isShared_4748_ = v_isSharedCheck_4759_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_v_4745_);
lean_inc(v_k_4744_);
lean_dec(v_l_4737_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4759_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4751_; 
v___x_4749_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4738_, 2);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 4, v_r_4738_);
lean_ctor_set(v___x_4747_, 3, v_r_4738_);
lean_ctor_set(v___x_4747_, 2, v_v_4644_);
lean_ctor_set(v___x_4747_, 1, v_k_4643_);
lean_ctor_set(v___x_4747_, 0, v___x_4653_);
v___x_4751_ = v___x_4747_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v_r_4738_);
v___x_4751_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4753_; 
lean_inc(v_r_4738_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 3, v_r_4738_);
lean_ctor_set(v___x_4742_, 0, v___x_4653_);
v___x_4753_ = v___x_4742_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_k_4739_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_v_4740_);
lean_ctor_set(v_reuseFailAlloc_4757_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4757_, 4, v_r_4738_);
v___x_4753_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4755_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4753_);
lean_ctor_set(v___x_4648_, 3, v___x_4751_);
lean_ctor_set(v___x_4648_, 2, v_v_4745_);
lean_ctor_set(v___x_4648_, 1, v_k_4744_);
lean_ctor_set(v___x_4648_, 0, v___x_4749_);
v___x_4755_ = v___x_4648_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_k_4744_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_v_4745_);
lean_ctor_set(v_reuseFailAlloc_4756_, 3, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4756_, 4, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
}
else
{
lean_object* v_r_4766_; 
v_r_4766_ = lean_ctor_get(v_impl_4652_, 4);
lean_inc(v_r_4766_);
if (lean_obj_tag(v_r_4766_) == 0)
{
lean_object* v_k_4767_; lean_object* v_v_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4779_; 
v_k_4767_ = lean_ctor_get(v_impl_4652_, 1);
v_v_4768_ = lean_ctor_get(v_impl_4652_, 2);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4779_ == 0)
{
lean_object* v_unused_4780_; lean_object* v_unused_4781_; lean_object* v_unused_4782_; 
v_unused_4780_ = lean_ctor_get(v_impl_4652_, 4);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4781_);
v_unused_4782_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4782_);
v___x_4770_ = v_impl_4652_;
v_isShared_4771_ = v_isSharedCheck_4779_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_v_4768_);
lean_inc(v_k_4767_);
lean_dec(v_impl_4652_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4779_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4772_ = lean_unsigned_to_nat(3u);
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 4, v_l_4737_);
lean_ctor_set(v___x_4770_, 2, v_v_4644_);
lean_ctor_set(v___x_4770_, 1, v_k_4643_);
lean_ctor_set(v___x_4770_, 0, v___x_4653_);
v___x_4774_ = v___x_4770_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_l_4737_);
lean_ctor_set(v_reuseFailAlloc_4778_, 4, v_l_4737_);
v___x_4774_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4776_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_r_4766_);
lean_ctor_set(v___x_4648_, 3, v___x_4774_);
lean_ctor_set(v___x_4648_, 2, v_v_4768_);
lean_ctor_set(v___x_4648_, 1, v_k_4767_);
lean_ctor_set(v___x_4648_, 0, v___x_4772_);
v___x_4776_ = v___x_4648_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4772_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_k_4767_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_v_4768_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v___x_4774_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_r_4766_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_unsigned_to_nat(2u);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_impl_4652_);
lean_ctor_set(v___x_4648_, 3, v_r_4766_);
lean_ctor_set(v___x_4648_, 0, v___x_4783_);
v___x_4785_ = v___x_4648_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_r_4766_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v_impl_4652_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
else
{
lean_object* v___x_4788_; 
lean_dec(v_v_4644_);
lean_dec(v_k_4643_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 2, v_v_4640_);
lean_ctor_set(v___x_4648_, 1, v_k_4639_);
v___x_4788_ = v___x_4648_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_size_4642_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_r_4646_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
else
{
lean_object* v_impl_4790_; lean_object* v___x_4791_; 
lean_dec(v_size_4642_);
v_impl_4790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4639_, v_v_4640_, v_l_4645_);
v___x_4791_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4646_) == 0)
{
lean_object* v_size_4792_; lean_object* v_size_4793_; lean_object* v_k_4794_; lean_object* v_v_4795_; lean_object* v_l_4796_; lean_object* v_r_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v_size_4792_ = lean_ctor_get(v_r_4646_, 0);
v_size_4793_ = lean_ctor_get(v_impl_4790_, 0);
lean_inc(v_size_4793_);
v_k_4794_ = lean_ctor_get(v_impl_4790_, 1);
lean_inc(v_k_4794_);
v_v_4795_ = lean_ctor_get(v_impl_4790_, 2);
lean_inc(v_v_4795_);
v_l_4796_ = lean_ctor_get(v_impl_4790_, 3);
lean_inc(v_l_4796_);
v_r_4797_ = lean_ctor_get(v_impl_4790_, 4);
lean_inc(v_r_4797_);
v___x_4798_ = lean_unsigned_to_nat(3u);
v___x_4799_ = lean_nat_mul(v___x_4798_, v_size_4792_);
v___x_4800_ = lean_nat_dec_lt(v___x_4799_, v_size_4793_);
lean_dec(v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v_r_4797_);
lean_dec(v_l_4796_);
lean_dec(v_v_4795_);
lean_dec(v_k_4794_);
v___x_4801_ = lean_nat_add(v___x_4791_, v_size_4793_);
lean_dec(v_size_4793_);
v___x_4802_ = lean_nat_add(v___x_4801_, v_size_4792_);
lean_dec(v___x_4801_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 3, v_impl_4790_);
lean_ctor_set(v___x_4648_, 0, v___x_4802_);
v___x_4804_ = v___x_4648_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_impl_4790_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v_r_4646_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
else
{
lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4871_; 
v_isSharedCheck_4871_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; lean_object* v_unused_4875_; lean_object* v_unused_4876_; 
v_unused_4872_ = lean_ctor_get(v_impl_4790_, 4);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_impl_4790_, 2);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_impl_4790_, 1);
lean_dec(v_unused_4875_);
v_unused_4876_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4876_);
v___x_4807_ = v_impl_4790_;
v_isShared_4808_ = v_isSharedCheck_4871_;
goto v_resetjp_4806_;
}
else
{
lean_dec(v_impl_4790_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4871_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v_size_4809_; lean_object* v_size_4810_; lean_object* v_k_4811_; lean_object* v_v_4812_; lean_object* v_l_4813_; lean_object* v_r_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_size_4809_ = lean_ctor_get(v_l_4796_, 0);
v_size_4810_ = lean_ctor_get(v_r_4797_, 0);
v_k_4811_ = lean_ctor_get(v_r_4797_, 1);
v_v_4812_ = lean_ctor_get(v_r_4797_, 2);
v_l_4813_ = lean_ctor_get(v_r_4797_, 3);
v_r_4814_ = lean_ctor_get(v_r_4797_, 4);
v___x_4815_ = lean_unsigned_to_nat(2u);
v___x_4816_ = lean_nat_mul(v___x_4815_, v_size_4809_);
v___x_4817_ = lean_nat_dec_lt(v_size_4810_, v___x_4816_);
lean_dec(v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4846_; 
lean_inc(v_r_4814_);
lean_inc(v_l_4813_);
lean_inc(v_v_4812_);
lean_inc(v_k_4811_);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_r_4797_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; lean_object* v_unused_4848_; lean_object* v_unused_4849_; lean_object* v_unused_4850_; lean_object* v_unused_4851_; 
v_unused_4847_ = lean_ctor_get(v_r_4797_, 4);
lean_dec(v_unused_4847_);
v_unused_4848_ = lean_ctor_get(v_r_4797_, 3);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_r_4797_, 2);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_r_4797_, 1);
lean_dec(v_unused_4850_);
v_unused_4851_ = lean_ctor_get(v_r_4797_, 0);
lean_dec(v_unused_4851_);
v___x_4819_ = v_r_4797_;
v_isShared_4820_ = v_isSharedCheck_4846_;
goto v_resetjp_4818_;
}
else
{
lean_dec(v_r_4797_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4846_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___x_4834_; lean_object* v___y_4836_; 
v___x_4821_ = lean_nat_add(v___x_4791_, v_size_4793_);
lean_dec(v_size_4793_);
v___x_4822_ = lean_nat_add(v___x_4821_, v_size_4792_);
lean_dec(v___x_4821_);
v___x_4834_ = lean_nat_add(v___x_4791_, v_size_4809_);
if (lean_obj_tag(v_l_4813_) == 0)
{
lean_object* v_size_4844_; 
v_size_4844_ = lean_ctor_get(v_l_4813_, 0);
lean_inc(v_size_4844_);
v___y_4836_ = v_size_4844_;
goto v___jp_4835_;
}
else
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_unsigned_to_nat(0u);
v___y_4836_ = v___x_4845_;
goto v___jp_4835_;
}
v___jp_4823_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_nat_add(v___y_4824_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec(v___y_4824_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 4, v_r_4646_);
lean_ctor_set(v___x_4819_, 3, v_r_4814_);
lean_ctor_set(v___x_4819_, 2, v_v_4644_);
lean_ctor_set(v___x_4819_, 1, v_k_4643_);
lean_ctor_set(v___x_4819_, 0, v___x_4827_);
v___x_4829_ = v___x_4819_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4833_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4833_, 3, v_r_4814_);
lean_ctor_set(v_reuseFailAlloc_4833_, 4, v_r_4646_);
v___x_4829_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4831_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 4, v___x_4829_);
lean_ctor_set(v___x_4807_, 3, v___y_4825_);
lean_ctor_set(v___x_4807_, 2, v_v_4812_);
lean_ctor_set(v___x_4807_, 1, v_k_4811_);
lean_ctor_set(v___x_4807_, 0, v___x_4822_);
v___x_4831_ = v___x_4807_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_k_4811_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_v_4812_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v___y_4825_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
v___jp_4835_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_nat_add(v___x_4834_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec(v___x_4834_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_l_4813_);
lean_ctor_set(v___x_4648_, 3, v_l_4796_);
lean_ctor_set(v___x_4648_, 2, v_v_4795_);
lean_ctor_set(v___x_4648_, 1, v_k_4794_);
lean_ctor_set(v___x_4648_, 0, v___x_4837_);
v___x_4839_ = v___x_4648_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_v_4795_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_l_4796_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_l_4813_);
v___x_4839_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_nat_add(v___x_4791_, v_size_4792_);
if (lean_obj_tag(v_r_4814_) == 0)
{
lean_object* v_size_4841_; 
v_size_4841_ = lean_ctor_get(v_r_4814_, 0);
lean_inc(v_size_4841_);
v___y_4824_ = v___x_4840_;
v___y_4825_ = v___x_4839_;
v___y_4826_ = v_size_4841_;
goto v___jp_4823_;
}
else
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_unsigned_to_nat(0u);
v___y_4824_ = v___x_4840_;
v___y_4825_ = v___x_4839_;
v___y_4826_ = v___x_4842_;
goto v___jp_4823_;
}
}
}
}
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4857_; 
lean_del_object(v___x_4648_);
v___x_4852_ = lean_nat_add(v___x_4791_, v_size_4793_);
lean_dec(v_size_4793_);
v___x_4853_ = lean_nat_add(v___x_4852_, v_size_4792_);
lean_dec(v___x_4852_);
v___x_4854_ = lean_nat_add(v___x_4791_, v_size_4792_);
v___x_4855_ = lean_nat_add(v___x_4854_, v_size_4810_);
lean_dec(v___x_4854_);
lean_inc_ref(v_r_4646_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 4, v_r_4646_);
lean_ctor_set(v___x_4807_, 3, v_r_4797_);
lean_ctor_set(v___x_4807_, 2, v_v_4644_);
lean_ctor_set(v___x_4807_, 1, v_k_4643_);
lean_ctor_set(v___x_4807_, 0, v___x_4855_);
v___x_4857_ = v___x_4807_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4870_, 3, v_r_4797_);
lean_ctor_set(v_reuseFailAlloc_4870_, 4, v_r_4646_);
v___x_4857_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
v_isSharedCheck_4864_ = !lean_is_exclusive(v_r_4646_);
if (v_isSharedCheck_4864_ == 0)
{
lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; lean_object* v_unused_4868_; lean_object* v_unused_4869_; 
v_unused_4865_ = lean_ctor_get(v_r_4646_, 4);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_r_4646_, 3);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_r_4646_, 2);
lean_dec(v_unused_4867_);
v_unused_4868_ = lean_ctor_get(v_r_4646_, 1);
lean_dec(v_unused_4868_);
v_unused_4869_ = lean_ctor_get(v_r_4646_, 0);
lean_dec(v_unused_4869_);
v___x_4859_ = v_r_4646_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_dec(v_r_4646_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
lean_ctor_set(v___x_4859_, 4, v___x_4857_);
lean_ctor_set(v___x_4859_, 3, v_l_4796_);
lean_ctor_set(v___x_4859_, 2, v_v_4795_);
lean_ctor_set(v___x_4859_, 1, v_k_4794_);
lean_ctor_set(v___x_4859_, 0, v___x_4853_);
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v___x_4853_);
lean_ctor_set(v_reuseFailAlloc_4863_, 1, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4863_, 2, v_v_4795_);
lean_ctor_set(v_reuseFailAlloc_4863_, 3, v_l_4796_);
lean_ctor_set(v_reuseFailAlloc_4863_, 4, v___x_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4877_; 
v_l_4877_ = lean_ctor_get(v_impl_4790_, 3);
lean_inc(v_l_4877_);
if (lean_obj_tag(v_l_4877_) == 0)
{
lean_object* v_r_4878_; lean_object* v_k_4879_; lean_object* v_v_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4891_; 
v_r_4878_ = lean_ctor_get(v_impl_4790_, 4);
v_k_4879_ = lean_ctor_get(v_impl_4790_, 1);
v_v_4880_ = lean_ctor_get(v_impl_4790_, 2);
v_isSharedCheck_4891_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4891_ == 0)
{
lean_object* v_unused_4892_; lean_object* v_unused_4893_; 
v_unused_4892_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4892_);
v_unused_4893_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4893_);
v___x_4882_ = v_impl_4790_;
v_isShared_4883_ = v_isSharedCheck_4891_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_r_4878_);
lean_inc(v_v_4880_);
lean_inc(v_k_4879_);
lean_dec(v_impl_4790_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4891_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4884_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4878_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 3, v_r_4878_);
lean_ctor_set(v___x_4882_, 2, v_v_4644_);
lean_ctor_set(v___x_4882_, 1, v_k_4643_);
lean_ctor_set(v___x_4882_, 0, v___x_4791_);
v___x_4886_ = v___x_4882_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4890_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4890_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4890_, 3, v_r_4878_);
lean_ctor_set(v_reuseFailAlloc_4890_, 4, v_r_4878_);
v___x_4886_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
lean_object* v___x_4888_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4886_);
lean_ctor_set(v___x_4648_, 3, v_l_4877_);
lean_ctor_set(v___x_4648_, 2, v_v_4880_);
lean_ctor_set(v___x_4648_, 1, v_k_4879_);
lean_ctor_set(v___x_4648_, 0, v___x_4884_);
v___x_4888_ = v___x_4648_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_k_4879_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_v_4880_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_l_4877_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
else
{
lean_object* v_r_4894_; 
v_r_4894_ = lean_ctor_get(v_impl_4790_, 4);
lean_inc(v_r_4894_);
if (lean_obj_tag(v_r_4894_) == 0)
{
lean_object* v_k_4895_; lean_object* v_v_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4919_; 
v_k_4895_ = lean_ctor_get(v_impl_4790_, 1);
v_v_4896_ = lean_ctor_get(v_impl_4790_, 2);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; lean_object* v_unused_4921_; lean_object* v_unused_4922_; 
v_unused_4920_ = lean_ctor_get(v_impl_4790_, 4);
lean_dec(v_unused_4920_);
v_unused_4921_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4921_);
v_unused_4922_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4922_);
v___x_4898_ = v_impl_4790_;
v_isShared_4899_ = v_isSharedCheck_4919_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_v_4896_);
lean_inc(v_k_4895_);
lean_dec(v_impl_4790_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4919_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_k_4900_; lean_object* v_v_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4915_; 
v_k_4900_ = lean_ctor_get(v_r_4894_, 1);
v_v_4901_ = lean_ctor_get(v_r_4894_, 2);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_r_4894_);
if (v_isSharedCheck_4915_ == 0)
{
lean_object* v_unused_4916_; lean_object* v_unused_4917_; lean_object* v_unused_4918_; 
v_unused_4916_ = lean_ctor_get(v_r_4894_, 4);
lean_dec(v_unused_4916_);
v_unused_4917_ = lean_ctor_get(v_r_4894_, 3);
lean_dec(v_unused_4917_);
v_unused_4918_ = lean_ctor_get(v_r_4894_, 0);
lean_dec(v_unused_4918_);
v___x_4903_ = v_r_4894_;
v_isShared_4904_ = v_isSharedCheck_4915_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_v_4901_);
lean_inc(v_k_4900_);
lean_dec(v_r_4894_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4915_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4905_ = lean_unsigned_to_nat(3u);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 4, v_l_4877_);
lean_ctor_set(v___x_4903_, 3, v_l_4877_);
lean_ctor_set(v___x_4903_, 2, v_v_4896_);
lean_ctor_set(v___x_4903_, 1, v_k_4895_);
lean_ctor_set(v___x_4903_, 0, v___x_4791_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v_k_4895_);
lean_ctor_set(v_reuseFailAlloc_4914_, 2, v_v_4896_);
lean_ctor_set(v_reuseFailAlloc_4914_, 3, v_l_4877_);
lean_ctor_set(v_reuseFailAlloc_4914_, 4, v_l_4877_);
v___x_4907_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4909_; 
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 4, v_l_4877_);
lean_ctor_set(v___x_4898_, 2, v_v_4644_);
lean_ctor_set(v___x_4898_, 1, v_k_4643_);
lean_ctor_set(v___x_4898_, 0, v___x_4791_);
v___x_4909_ = v___x_4898_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_l_4877_);
lean_ctor_set(v_reuseFailAlloc_4913_, 4, v_l_4877_);
v___x_4909_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4911_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4909_);
lean_ctor_set(v___x_4648_, 3, v___x_4907_);
lean_ctor_set(v___x_4648_, 2, v_v_4901_);
lean_ctor_set(v___x_4648_, 1, v_k_4900_);
lean_ctor_set(v___x_4648_, 0, v___x_4905_);
v___x_4911_ = v___x_4648_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_k_4900_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_v_4901_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
}
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4925_; 
v___x_4923_ = lean_unsigned_to_nat(2u);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_r_4894_);
lean_ctor_set(v___x_4648_, 3, v_impl_4790_);
lean_ctor_set(v___x_4648_, 0, v___x_4923_);
v___x_4925_ = v___x_4648_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4926_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4926_, 3, v_impl_4790_);
lean_ctor_set(v_reuseFailAlloc_4926_, 4, v_r_4894_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = lean_unsigned_to_nat(1u);
v___x_4929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
lean_ctor_set(v___x_4929_, 1, v_k_4639_);
lean_ctor_set(v___x_4929_, 2, v_v_4640_);
lean_ctor_set(v___x_4929_, 3, v_t_4641_);
lean_ctor_set(v___x_4929_, 4, v_t_4641_);
return v___x_4929_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_4930_, lean_object* v_t_4931_){
_start:
{
if (lean_obj_tag(v_t_4931_) == 0)
{
lean_object* v_k_4932_; lean_object* v_l_4933_; lean_object* v_r_4934_; uint8_t v___x_4935_; 
v_k_4932_ = lean_ctor_get(v_t_4931_, 1);
v_l_4933_ = lean_ctor_get(v_t_4931_, 3);
v_r_4934_ = lean_ctor_get(v_t_4931_, 4);
v___x_4935_ = lean_nat_dec_lt(v_k_4932_, v_k_4930_);
if (v___x_4935_ == 0)
{
uint8_t v___x_4936_; 
v___x_4936_ = lean_nat_dec_eq(v_k_4932_, v_k_4930_);
if (v___x_4936_ == 0)
{
v_t_4931_ = v_r_4934_;
goto _start;
}
else
{
return v___x_4936_;
}
}
else
{
v_t_4931_ = v_l_4933_;
goto _start;
}
}
else
{
uint8_t v___x_4939_; 
v___x_4939_ = 0;
return v___x_4939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_4940_, lean_object* v_t_4941_){
_start:
{
uint8_t v_res_4942_; lean_object* v_r_4943_; 
v_res_4942_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4940_, v_t_4941_);
lean_dec(v_t_4941_);
lean_dec(v_k_4940_);
v_r_4943_ = lean_box(v_res_4942_);
return v_r_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_4944_, lean_object* v_e_4945_){
_start:
{
lean_object* v_defaultInstances_4946_; lean_object* v_priorities_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4974_; 
v_defaultInstances_4946_ = lean_ctor_get(v_d_4944_, 0);
v_priorities_4947_ = lean_ctor_get(v_d_4944_, 1);
v_isSharedCheck_4974_ = !lean_is_exclusive(v_d_4944_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4949_ = v_d_4944_;
v_isShared_4950_ = v_isSharedCheck_4974_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_priorities_4947_);
lean_inc(v_defaultInstances_4946_);
lean_dec(v_d_4944_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4974_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v_className_4951_; lean_object* v_instanceName_4952_; lean_object* v_priority_4953_; lean_object* v___y_4955_; uint8_t v___x_4971_; 
v_className_4951_ = lean_ctor_get(v_e_4945_, 0);
lean_inc(v_className_4951_);
v_instanceName_4952_ = lean_ctor_get(v_e_4945_, 1);
lean_inc(v_instanceName_4952_);
v_priority_4953_ = lean_ctor_get(v_e_4945_, 2);
lean_inc(v_priority_4953_);
lean_dec_ref(v_e_4945_);
v___x_4971_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_4953_, v_priorities_4947_);
if (v___x_4971_ == 0)
{
lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4972_ = lean_box(0);
lean_inc(v_priority_4953_);
v___x_4973_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_4953_, v___x_4972_, v_priorities_4947_);
v___y_4955_ = v___x_4973_;
goto v___jp_4954_;
}
else
{
v___y_4955_ = v_priorities_4947_;
goto v___jp_4954_;
}
v___jp_4954_:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_4946_, v_className_4951_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4957_, 0, v_instanceName_4952_);
lean_ctor_set(v___x_4957_, 1, v_priority_4953_);
v___x_4958_ = lean_box(0);
v___x_4959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4951_, v___x_4959_, v_defaultInstances_4946_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___y_4955_);
lean_ctor_set(v___x_4949_, 0, v___x_4960_);
v___x_4962_ = v___x_4949_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4960_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___y_4955_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
else
{
lean_object* v_val_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4969_; 
v_val_4964_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_val_4964_);
lean_dec_ref(v___x_4956_);
v___x_4965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4965_, 0, v_instanceName_4952_);
lean_ctor_set(v___x_4965_, 1, v_priority_4953_);
v___x_4966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
lean_ctor_set(v___x_4966_, 1, v_val_4964_);
v___x_4967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4951_, v___x_4966_, v_defaultInstances_4946_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___y_4955_);
lean_ctor_set(v___x_4949_, 0, v___x_4967_);
v___x_4969_ = v___x_4949_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4970_, 1, v___y_4955_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_4975_, lean_object* v_k_4976_, lean_object* v_t_4977_){
_start:
{
uint8_t v___x_4978_; 
v___x_4978_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4976_, v_t_4977_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_4979_, lean_object* v_k_4980_, lean_object* v_t_4981_){
_start:
{
uint8_t v_res_4982_; lean_object* v_r_4983_; 
v_res_4982_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_4979_, v_k_4980_, v_t_4981_);
lean_dec(v_t_4981_);
lean_dec(v_k_4980_);
v_r_4983_ = lean_box(v_res_4982_);
return v_r_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_4984_, lean_object* v_k_4985_, lean_object* v_v_4986_, lean_object* v_t_4987_, lean_object* v_hl_4988_){
_start:
{
lean_object* v___x_4989_; 
v___x_4989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4985_, v_v_4986_, v_t_4987_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_4990_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = lean_array_mk(v_es_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4992_, size_t v_i_4993_, size_t v_stop_4994_, lean_object* v_b_4995_){
_start:
{
uint8_t v___x_4996_; 
v___x_4996_ = lean_usize_dec_eq(v_i_4993_, v_stop_4994_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; lean_object* v___x_4998_; size_t v___x_4999_; size_t v___x_5000_; 
v___x_4997_ = lean_array_uget_borrowed(v_as_4992_, v_i_4993_);
lean_inc(v___x_4997_);
v___x_4998_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_4995_, v___x_4997_);
v___x_4999_ = ((size_t)1ULL);
v___x_5000_ = lean_usize_add(v_i_4993_, v___x_4999_);
v_i_4993_ = v___x_5000_;
v_b_4995_ = v___x_4998_;
goto _start;
}
else
{
return v_b_4995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5002_, lean_object* v_i_5003_, lean_object* v_stop_5004_, lean_object* v_b_5005_){
_start:
{
size_t v_i_boxed_5006_; size_t v_stop_boxed_5007_; lean_object* v_res_5008_; 
v_i_boxed_5006_ = lean_unbox_usize(v_i_5003_);
lean_dec(v_i_5003_);
v_stop_boxed_5007_ = lean_unbox_usize(v_stop_5004_);
lean_dec(v_stop_5004_);
v_res_5008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_5002_, v_i_boxed_5006_, v_stop_boxed_5007_, v_b_5005_);
lean_dec_ref(v_as_5002_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_5009_, size_t v_i_5010_, size_t v_stop_5011_, lean_object* v_b_5012_){
_start:
{
lean_object* v___y_5014_; uint8_t v___x_5018_; 
v___x_5018_ = lean_usize_dec_eq(v_i_5010_, v_stop_5011_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; uint8_t v___x_5022_; 
v___x_5019_ = lean_array_uget_borrowed(v_as_5009_, v_i_5010_);
v___x_5020_ = lean_unsigned_to_nat(0u);
v___x_5021_ = lean_array_get_size(v___x_5019_);
v___x_5022_ = lean_nat_dec_lt(v___x_5020_, v___x_5021_);
if (v___x_5022_ == 0)
{
v___y_5014_ = v_b_5012_;
goto v___jp_5013_;
}
else
{
uint8_t v___x_5023_; 
v___x_5023_ = lean_nat_dec_le(v___x_5021_, v___x_5021_);
if (v___x_5023_ == 0)
{
if (v___x_5022_ == 0)
{
v___y_5014_ = v_b_5012_;
goto v___jp_5013_;
}
else
{
size_t v___x_5024_; size_t v___x_5025_; lean_object* v___x_5026_; 
v___x_5024_ = ((size_t)0ULL);
v___x_5025_ = lean_usize_of_nat(v___x_5021_);
v___x_5026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5019_, v___x_5024_, v___x_5025_, v_b_5012_);
v___y_5014_ = v___x_5026_;
goto v___jp_5013_;
}
}
else
{
size_t v___x_5027_; size_t v___x_5028_; lean_object* v___x_5029_; 
v___x_5027_ = ((size_t)0ULL);
v___x_5028_ = lean_usize_of_nat(v___x_5021_);
v___x_5029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5019_, v___x_5027_, v___x_5028_, v_b_5012_);
v___y_5014_ = v___x_5029_;
goto v___jp_5013_;
}
}
}
else
{
return v_b_5012_;
}
v___jp_5013_:
{
size_t v___x_5015_; size_t v___x_5016_; 
v___x_5015_ = ((size_t)1ULL);
v___x_5016_ = lean_usize_add(v_i_5010_, v___x_5015_);
v_i_5010_ = v___x_5016_;
v_b_5012_ = v___y_5014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5030_, lean_object* v_i_5031_, lean_object* v_stop_5032_, lean_object* v_b_5033_){
_start:
{
size_t v_i_boxed_5034_; size_t v_stop_boxed_5035_; lean_object* v_res_5036_; 
v_i_boxed_5034_ = lean_unbox_usize(v_i_5031_);
lean_dec(v_i_5031_);
v_stop_boxed_5035_ = lean_unbox_usize(v_stop_5032_);
lean_dec(v_stop_5032_);
v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5030_, v_i_boxed_5034_, v_stop_boxed_5035_, v_b_5033_);
lean_dec_ref(v_as_5030_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5037_, lean_object* v_as_5038_){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5039_ = lean_unsigned_to_nat(0u);
v___x_5040_ = lean_array_get_size(v_as_5038_);
v___x_5041_ = lean_nat_dec_lt(v___x_5039_, v___x_5040_);
if (v___x_5041_ == 0)
{
return v_initState_5037_;
}
else
{
uint8_t v___x_5042_; 
v___x_5042_ = lean_nat_dec_le(v___x_5040_, v___x_5040_);
if (v___x_5042_ == 0)
{
if (v___x_5041_ == 0)
{
return v_initState_5037_;
}
else
{
size_t v___x_5043_; size_t v___x_5044_; lean_object* v___x_5045_; 
v___x_5043_ = ((size_t)0ULL);
v___x_5044_ = lean_usize_of_nat(v___x_5040_);
v___x_5045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5038_, v___x_5043_, v___x_5044_, v_initState_5037_);
return v___x_5045_;
}
}
else
{
size_t v___x_5046_; size_t v___x_5047_; lean_object* v___x_5048_; 
v___x_5046_ = ((size_t)0ULL);
v___x_5047_ = lean_usize_of_nat(v___x_5040_);
v___x_5048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5038_, v___x_5046_, v___x_5047_, v_initState_5037_);
return v___x_5048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5049_, lean_object* v_as_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5049_, v_as_5050_);
lean_dec_ref(v_as_5050_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5052_){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5054_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5053_, v_es_5052_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5055_);
lean_dec_ref(v_es_5055_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5074_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v___x_5081_; lean_object* v_nextMacroScope_5082_; lean_object* v_ngen_5083_; lean_object* v_auxDeclNGen_5084_; lean_object* v_traceState_5085_; lean_object* v_messages_5086_; lean_object* v_infoState_5087_; lean_object* v_snapshotTasks_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5114_; 
v___x_5081_ = lean_st_ref_take(v___y_5079_);
v_nextMacroScope_5082_ = lean_ctor_get(v___x_5081_, 1);
v_ngen_5083_ = lean_ctor_get(v___x_5081_, 2);
v_auxDeclNGen_5084_ = lean_ctor_get(v___x_5081_, 3);
v_traceState_5085_ = lean_ctor_get(v___x_5081_, 4);
v_messages_5086_ = lean_ctor_get(v___x_5081_, 6);
v_infoState_5087_ = lean_ctor_get(v___x_5081_, 7);
v_snapshotTasks_5088_ = lean_ctor_get(v___x_5081_, 8);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; lean_object* v_unused_5116_; 
v_unused_5115_ = lean_ctor_get(v___x_5081_, 5);
lean_dec(v_unused_5115_);
v_unused_5116_ = lean_ctor_get(v___x_5081_, 0);
lean_dec(v_unused_5116_);
v___x_5090_ = v___x_5081_;
v_isShared_5091_ = v_isSharedCheck_5114_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snapshotTasks_5088_);
lean_inc(v_infoState_5087_);
lean_inc(v_messages_5086_);
lean_inc(v_traceState_5085_);
lean_inc(v_auxDeclNGen_5084_);
lean_inc(v_ngen_5083_);
lean_inc(v_nextMacroScope_5082_);
lean_dec(v___x_5081_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5114_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5092_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 5, v___x_5092_);
lean_ctor_set(v___x_5090_, 0, v_env_5077_);
v___x_5094_ = v___x_5090_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_env_5077_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v_nextMacroScope_5082_);
lean_ctor_set(v_reuseFailAlloc_5113_, 2, v_ngen_5083_);
lean_ctor_set(v_reuseFailAlloc_5113_, 3, v_auxDeclNGen_5084_);
lean_ctor_set(v_reuseFailAlloc_5113_, 4, v_traceState_5085_);
lean_ctor_set(v_reuseFailAlloc_5113_, 5, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5113_, 6, v_messages_5086_);
lean_ctor_set(v_reuseFailAlloc_5113_, 7, v_infoState_5087_);
lean_ctor_set(v_reuseFailAlloc_5113_, 8, v_snapshotTasks_5088_);
v___x_5094_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v_mctx_5097_; lean_object* v_zetaDeltaFVarIds_5098_; lean_object* v_postponed_5099_; lean_object* v_diag_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5111_; 
v___x_5095_ = lean_st_ref_set(v___y_5079_, v___x_5094_);
v___x_5096_ = lean_st_ref_take(v___y_5078_);
v_mctx_5097_ = lean_ctor_get(v___x_5096_, 0);
v_zetaDeltaFVarIds_5098_ = lean_ctor_get(v___x_5096_, 2);
v_postponed_5099_ = lean_ctor_get(v___x_5096_, 3);
v_diag_5100_ = lean_ctor_get(v___x_5096_, 4);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5111_ == 0)
{
lean_object* v_unused_5112_; 
v_unused_5112_ = lean_ctor_get(v___x_5096_, 1);
lean_dec(v_unused_5112_);
v___x_5102_ = v___x_5096_;
v_isShared_5103_ = v_isSharedCheck_5111_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_diag_5100_);
lean_inc(v_postponed_5099_);
lean_inc(v_zetaDeltaFVarIds_5098_);
lean_inc(v_mctx_5097_);
lean_dec(v___x_5096_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5111_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5104_; lean_object* v___x_5106_; 
v___x_5104_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 1, v___x_5104_);
v___x_5106_ = v___x_5102_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_mctx_5097_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v___x_5104_);
lean_ctor_set(v_reuseFailAlloc_5110_, 2, v_zetaDeltaFVarIds_5098_);
lean_ctor_set(v_reuseFailAlloc_5110_, 3, v_postponed_5099_);
lean_ctor_set(v_reuseFailAlloc_5110_, 4, v_diag_5100_);
v___x_5106_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5107_ = lean_st_ref_set(v___y_5078_, v___x_5106_);
v___x_5108_ = lean_box(0);
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5117_, v___y_5118_, v___y_5119_);
lean_dec(v___y_5119_);
lean_dec(v___y_5118_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5122_, v___y_5124_, v___y_5126_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
return v_res_5135_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5137_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5138_ = l_Lean_stringToMessageData(v___x_5137_);
return v___x_5138_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5140_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5141_ = l_Lean_stringToMessageData(v___x_5140_);
return v___x_5141_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5143_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5144_ = l_Lean_stringToMessageData(v___x_5143_);
return v___x_5144_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5147_ = l_Lean_stringToMessageData(v___x_5146_);
return v___x_5147_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
v___x_5149_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5150_ = l_Lean_stringToMessageData(v___x_5149_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5151_, lean_object* v_prio_5152_, lean_object* v_x_5153_, lean_object* v_type_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_Lean_Expr_getAppFn(v_type_5154_);
if (lean_obj_tag(v___x_5160_) == 4)
{
lean_object* v_declName_5161_; lean_object* v___y_5163_; lean_object* v___y_5164_; lean_object* v___y_5165_; lean_object* v___y_5166_; lean_object* v___x_5176_; lean_object* v_env_5177_; uint8_t v___x_5178_; 
v_declName_5161_ = lean_ctor_get(v___x_5160_, 0);
lean_inc_n(v_declName_5161_, 2);
lean_dec_ref(v___x_5160_);
v___x_5176_ = lean_st_ref_get(v___y_5158_);
v_env_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc_ref(v_env_5177_);
lean_dec(v___x_5176_);
v___x_5178_ = lean_is_class(v_env_5177_, v_declName_5161_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
lean_dec(v_prio_5152_);
v___x_5179_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5180_ = l_Lean_MessageData_ofConstName(v_declName_5151_, v___x_5178_);
v___x_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5179_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5181_);
lean_ctor_set(v___x_5183_, 1, v___x_5182_);
lean_inc(v_declName_5161_);
v___x_5184_ = l_Lean_MessageData_ofName(v_declName_5161_);
v___x_5185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5183_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
v___x_5186_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5185_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = l_Lean_MessageData_ofConstName(v_declName_5161_, v___x_5178_);
v___x_5189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5187_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
v___x_5190_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5189_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5191_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
return v___x_5192_;
}
else
{
v___y_5163_ = v___y_5155_;
v___y_5164_ = v___y_5156_;
v___y_5165_ = v___y_5157_;
v___y_5166_ = v___y_5158_;
goto v___jp_5162_;
}
v___jp_5162_:
{
lean_object* v___x_5167_; lean_object* v_env_5168_; lean_object* v___x_5169_; lean_object* v_toEnvExtension_5170_; lean_object* v_asyncMode_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5167_ = lean_st_ref_get(v___y_5166_);
v_env_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc_ref(v_env_5168_);
lean_dec(v___x_5167_);
v___x_5169_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5170_ = lean_ctor_get(v___x_5169_, 0);
v_asyncMode_5171_ = lean_ctor_get(v_toEnvExtension_5170_, 2);
v___x_5172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5172_, 0, v_declName_5161_);
lean_ctor_set(v___x_5172_, 1, v_declName_5151_);
lean_ctor_set(v___x_5172_, 2, v_prio_5152_);
v___x_5173_ = lean_box(0);
v___x_5174_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5169_, v_env_5168_, v___x_5172_, v_asyncMode_5171_, v___x_5173_);
v___x_5175_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5174_, v___y_5164_, v___y_5166_);
return v___x_5175_;
}
}
else
{
lean_object* v___x_5193_; uint8_t v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
lean_dec_ref(v___x_5160_);
lean_dec(v_prio_5152_);
v___x_5193_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5194_ = 0;
v___x_5195_ = l_Lean_MessageData_ofConstName(v_declName_5151_, v___x_5194_);
v___x_5196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5193_);
lean_ctor_set(v___x_5196_, 1, v___x_5195_);
v___x_5197_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5196_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5198_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
return v___x_5199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5200_, lean_object* v_prio_5201_, lean_object* v_x_5202_, lean_object* v_type_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5200_, v_prio_5201_, v_x_5202_, v_type_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec_ref(v_type_5203_);
lean_dec_ref(v_x_5202_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5210_, lean_object* v_prio_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v___x_5217_; lean_object* v_env_5218_; uint8_t v___x_5219_; lean_object* v___x_5220_; 
v___x_5217_ = lean_st_ref_get(v_a_5215_);
v_env_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc_ref(v_env_5218_);
lean_dec(v___x_5217_);
v___x_5219_ = 0;
lean_inc(v_declName_5210_);
v___x_5220_ = l_Lean_Environment_find_x3f(v_env_5218_, v_declName_5210_, v___x_5219_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_dec(v_prio_5211_);
v___x_5221_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5222_ = l_Lean_MessageData_ofConstName(v_declName_5210_, v___x_5219_);
v___x_5223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5221_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
v___x_5224_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
v___x_5226_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5225_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_);
return v___x_5226_;
}
else
{
lean_object* v_val_5227_; lean_object* v___f_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v_val_5227_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_val_5227_);
lean_dec_ref(v___x_5220_);
v___f_5228_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5228_, 0, v_declName_5210_);
lean_closure_set(v___f_5228_, 1, v_prio_5211_);
v___x_5229_ = l_Lean_ConstantInfo_type(v_val_5227_);
lean_dec(v_val_5227_);
v___x_5230_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5229_, v___f_5228_, v___x_5219_, v___x_5219_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_);
return v___x_5230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5231_, lean_object* v_prio_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Lean_Meta_addDefaultInstance(v_declName_5231_, v_prio_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_);
lean_dec(v_a_5236_);
lean_dec_ref(v_a_5235_);
lean_dec(v_a_5234_);
lean_dec_ref(v_a_5233_);
return v_res_5238_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5241_ = l_Lean_stringToMessageData(v___x_5240_);
return v___x_5241_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5243_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5244_ = l_Lean_stringToMessageData(v___x_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5248_, uint8_t v_kind_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___y_5259_; 
v___x_5253_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5254_ = l_Lean_MessageData_ofName(v_name_5248_);
v___x_5255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5253_);
lean_ctor_set(v___x_5255_, 1, v___x_5254_);
v___x_5256_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5257_, 0, v___x_5255_);
lean_ctor_set(v___x_5257_, 1, v___x_5256_);
switch(v_kind_5249_)
{
case 0:
{
lean_object* v___x_5266_; 
v___x_5266_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5259_ = v___x_5266_;
goto v___jp_5258_;
}
case 1:
{
lean_object* v___x_5267_; 
v___x_5267_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5259_ = v___x_5267_;
goto v___jp_5258_;
}
default: 
{
lean_object* v___x_5268_; 
v___x_5268_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5259_ = v___x_5268_;
goto v___jp_5258_;
}
}
v___jp_5258_:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
lean_inc_ref(v___y_5259_);
v___x_5260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5260_, 0, v___y_5259_);
v___x_5261_ = l_Lean_MessageData_ofFormat(v___x_5260_);
v___x_5262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5257_);
lean_ctor_set(v___x_5262_, 1, v___x_5261_);
v___x_5263_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5262_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
v___x_5265_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5264_, v___y_5250_, v___y_5251_);
return v___x_5265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5269_, lean_object* v_kind_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
uint8_t v_kind_boxed_5274_; lean_object* v_res_5275_; 
v_kind_boxed_5274_ = lean_unbox(v_kind_5270_);
v_res_5275_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5269_, v_kind_boxed_5274_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5276_, lean_object* v___x_5277_, lean_object* v___x_5278_, lean_object* v_declName_5279_, lean_object* v_stx_5280_, uint8_t v_kind_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5285_ = lean_unsigned_to_nat(1u);
v___x_5286_ = l_Lean_Syntax_getArg(v_stx_5280_, v___x_5285_);
v___x_5287_ = l_Lean_getAttrParamOptPrio(v___x_5286_, v___y_5282_, v___y_5283_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___y_5290_; lean_object* v___y_5291_; uint8_t v___x_5322_; uint8_t v___x_5323_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
lean_inc(v_a_5288_);
lean_dec_ref(v___x_5287_);
v___x_5322_ = 0;
v___x_5323_ = l_Lean_instBEqAttributeKind_beq(v_kind_5281_, v___x_5322_);
if (v___x_5323_ == 0)
{
lean_object* v___x_5324_; 
lean_dec(v_a_5288_);
lean_dec(v_declName_5279_);
lean_dec(v___x_5277_);
lean_dec(v___x_5276_);
v___x_5324_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5278_, v_kind_5281_, v___y_5282_, v___y_5283_);
return v___x_5324_;
}
else
{
lean_dec(v___x_5278_);
v___y_5290_ = v___y_5282_;
v___y_5291_ = v___y_5283_;
goto v___jp_5289_;
}
v___jp_5289_:
{
uint8_t v___x_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; size_t v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5292_ = 0;
v___x_5293_ = 1;
v___x_5294_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5295_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5296_ = lean_unsigned_to_nat(32u);
v___x_5297_ = lean_mk_empty_array_with_capacity(v___x_5296_);
v___x_5298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5299_ = ((size_t)5ULL);
lean_inc_n(v___x_5276_, 6);
v___x_5300_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5300_, 0, v___x_5298_);
lean_ctor_set(v___x_5300_, 1, v___x_5297_);
lean_ctor_set(v___x_5300_, 2, v___x_5276_);
lean_ctor_set(v___x_5300_, 3, v___x_5276_);
lean_ctor_set_usize(v___x_5300_, 4, v___x_5299_);
v___x_5301_ = lean_box(1);
lean_inc_ref(v___x_5300_);
v___x_5302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5295_);
lean_ctor_set(v___x_5302_, 1, v___x_5300_);
lean_ctor_set(v___x_5302_, 2, v___x_5301_);
v___x_5303_ = lean_mk_empty_array_with_capacity(v___x_5276_);
v___x_5304_ = lean_box(0);
lean_inc(v___x_5277_);
v___x_5305_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5305_, 0, v___x_5294_);
lean_ctor_set(v___x_5305_, 1, v___x_5277_);
lean_ctor_set(v___x_5305_, 2, v___x_5302_);
lean_ctor_set(v___x_5305_, 3, v___x_5303_);
lean_ctor_set(v___x_5305_, 4, v___x_5304_);
lean_ctor_set(v___x_5305_, 5, v___x_5276_);
lean_ctor_set(v___x_5305_, 6, v___x_5304_);
lean_ctor_set_uint8(v___x_5305_, sizeof(void*)*7, v___x_5292_);
lean_ctor_set_uint8(v___x_5305_, sizeof(void*)*7 + 1, v___x_5292_);
lean_ctor_set_uint8(v___x_5305_, sizeof(void*)*7 + 2, v___x_5292_);
lean_ctor_set_uint8(v___x_5305_, sizeof(void*)*7 + 3, v___x_5293_);
v___x_5306_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5276_);
lean_ctor_set(v___x_5306_, 1, v___x_5276_);
lean_ctor_set(v___x_5306_, 2, v___x_5276_);
lean_ctor_set(v___x_5306_, 3, v___x_5276_);
lean_ctor_set(v___x_5306_, 4, v___x_5295_);
lean_ctor_set(v___x_5306_, 5, v___x_5295_);
lean_ctor_set(v___x_5306_, 6, v___x_5295_);
lean_ctor_set(v___x_5306_, 7, v___x_5295_);
lean_ctor_set(v___x_5306_, 8, v___x_5295_);
lean_ctor_set(v___x_5306_, 9, v___x_5295_);
v___x_5307_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5308_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5306_);
lean_ctor_set(v___x_5309_, 1, v___x_5307_);
lean_ctor_set(v___x_5309_, 2, v___x_5277_);
lean_ctor_set(v___x_5309_, 3, v___x_5300_);
lean_ctor_set(v___x_5309_, 4, v___x_5308_);
v___x_5310_ = lean_st_mk_ref(v___x_5309_);
v___x_5311_ = l_Lean_Meta_addDefaultInstance(v_declName_5279_, v_a_5288_, v___x_5305_, v___x_5310_, v___y_5290_, v___y_5291_);
lean_dec_ref(v___x_5305_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5320_; 
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v___x_5311_, 0);
lean_dec(v_unused_5321_);
v___x_5313_ = v___x_5311_;
v_isShared_5314_ = v_isSharedCheck_5320_;
goto v_resetjp_5312_;
}
else
{
lean_dec(v___x_5311_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5320_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5318_; 
v___x_5315_ = lean_st_ref_get(v___x_5310_);
lean_dec(v___x_5310_);
lean_dec(v___x_5315_);
v___x_5316_ = lean_box(0);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5316_);
v___x_5318_ = v___x_5313_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5316_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
else
{
lean_dec(v___x_5310_);
return v___x_5311_;
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec(v_declName_5279_);
lean_dec(v___x_5278_);
lean_dec(v___x_5277_);
lean_dec(v___x_5276_);
v_a_5325_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5287_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5287_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5333_, lean_object* v___x_5334_, lean_object* v___x_5335_, lean_object* v_declName_5336_, lean_object* v_stx_5337_, lean_object* v_kind_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
uint8_t v_kind_boxed_5342_; lean_object* v_res_5343_; 
v_kind_boxed_5342_ = lean_unbox(v_kind_5338_);
v_res_5343_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5333_, v___x_5334_, v___x_5335_, v_declName_5336_, v_stx_5337_, v_kind_boxed_5342_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v_stx_5337_);
return v_res_5343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5345_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5346_ = l_Lean_stringToMessageData(v___x_5345_);
return v___x_5346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5349_ = l_Lean_stringToMessageData(v___x_5348_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5350_, lean_object* v_decl_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5355_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5356_ = l_Lean_MessageData_ofName(v___x_5350_);
v___x_5357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5355_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
v___x_5358_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5357_);
lean_ctor_set(v___x_5359_, 1, v___x_5358_);
v___x_5360_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5359_, v___y_5352_, v___y_5353_);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5361_, lean_object* v_decl_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5361_, v_decl_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v_decl_5362_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5400_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5401_ = l_Lean_registerBuiltinAttribute(v___x_5400_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v___x_5402_; uint8_t v___x_5403_; lean_object* v___x_5404_; 
lean_dec_ref(v___x_5401_);
v___x_5402_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5403_ = 0;
v___x_5404_ = l_Lean_registerTraceClass(v___x_5402_, v___x_5403_, v___x_5399_);
return v___x_5404_;
}
else
{
return v___x_5401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5407_, lean_object* v_name_5408_, uint8_t v_kind_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5408_, v_kind_5409_, v___y_5410_, v___y_5411_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5414_, lean_object* v_name_5415_, lean_object* v_kind_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
uint8_t v_kind_boxed_5420_; lean_object* v_res_5421_; 
v_kind_boxed_5420_ = lean_unbox(v_kind_5416_);
v_res_5421_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5414_, v_name_5415_, v_kind_boxed_5420_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5422_, lean_object* v_toPure_5423_, lean_object* v_____do__lift_5424_){
_start:
{
lean_object* v___x_5425_; lean_object* v_toEnvExtension_5426_; lean_object* v_asyncMode_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v_priorities_5430_; lean_object* v___x_5431_; 
v___x_5425_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5426_ = lean_ctor_get(v___x_5425_, 0);
v_asyncMode_5427_ = lean_ctor_get(v_toEnvExtension_5426_, 2);
v___x_5428_ = lean_box(0);
v___x_5429_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5422_, v___x_5425_, v_____do__lift_5424_, v_asyncMode_5427_, v___x_5428_);
v_priorities_5430_ = lean_ctor_get(v___x_5429_, 1);
lean_inc(v_priorities_5430_);
lean_dec(v___x_5429_);
v___x_5431_ = lean_apply_2(v_toPure_5423_, lean_box(0), v_priorities_5430_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5432_, lean_object* v_inst_5433_){
_start:
{
lean_object* v_toApplicative_5434_; lean_object* v_toBind_5435_; lean_object* v_getEnv_5436_; lean_object* v_toPure_5437_; lean_object* v___x_5438_; lean_object* v___f_5439_; lean_object* v___x_5440_; 
v_toApplicative_5434_ = lean_ctor_get(v_inst_5432_, 0);
lean_inc_ref(v_toApplicative_5434_);
v_toBind_5435_ = lean_ctor_get(v_inst_5432_, 1);
lean_inc(v_toBind_5435_);
lean_dec_ref(v_inst_5432_);
v_getEnv_5436_ = lean_ctor_get(v_inst_5433_, 0);
lean_inc(v_getEnv_5436_);
lean_dec_ref(v_inst_5433_);
v_toPure_5437_ = lean_ctor_get(v_toApplicative_5434_, 1);
lean_inc(v_toPure_5437_);
lean_dec_ref(v_toApplicative_5434_);
v___x_5438_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5439_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5439_, 0, v___x_5438_);
lean_closure_set(v___f_5439_, 1, v_toPure_5437_);
v___x_5440_ = lean_apply_4(v_toBind_5435_, lean_box(0), lean_box(0), v_getEnv_5436_, v___f_5439_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5441_, lean_object* v_inst_5442_, lean_object* v_inst_5443_){
_start:
{
lean_object* v___x_5444_; 
v___x_5444_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5442_, v_inst_5443_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5445_, lean_object* v_className_5446_, lean_object* v_toPure_5447_, lean_object* v_____do__lift_5448_){
_start:
{
lean_object* v___x_5449_; lean_object* v_toEnvExtension_5450_; lean_object* v_asyncMode_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v_defaultInstances_5454_; lean_object* v___x_5455_; 
v___x_5449_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5450_ = lean_ctor_get(v___x_5449_, 0);
v_asyncMode_5451_ = lean_ctor_get(v_toEnvExtension_5450_, 2);
v___x_5452_ = lean_box(0);
v___x_5453_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5445_, v___x_5449_, v_____do__lift_5448_, v_asyncMode_5451_, v___x_5452_);
v_defaultInstances_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v_defaultInstances_5454_);
lean_dec(v___x_5453_);
v___x_5455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5454_, v_className_5446_);
lean_dec(v_defaultInstances_5454_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5456_ = lean_box(0);
v___x_5457_ = lean_apply_2(v_toPure_5447_, lean_box(0), v___x_5456_);
return v___x_5457_;
}
else
{
lean_object* v_val_5458_; lean_object* v___x_5459_; 
v_val_5458_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_val_5458_);
lean_dec_ref(v___x_5455_);
v___x_5459_ = lean_apply_2(v_toPure_5447_, lean_box(0), v_val_5458_);
return v___x_5459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5460_, lean_object* v_className_5461_, lean_object* v_toPure_5462_, lean_object* v_____do__lift_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5460_, v_className_5461_, v_toPure_5462_, v_____do__lift_5463_);
lean_dec(v_className_5461_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5465_, lean_object* v_inst_5466_, lean_object* v_className_5467_){
_start:
{
lean_object* v_toApplicative_5468_; lean_object* v_toBind_5469_; lean_object* v_getEnv_5470_; lean_object* v_toPure_5471_; lean_object* v___x_5472_; lean_object* v___f_5473_; lean_object* v___x_5474_; 
v_toApplicative_5468_ = lean_ctor_get(v_inst_5465_, 0);
lean_inc_ref(v_toApplicative_5468_);
v_toBind_5469_ = lean_ctor_get(v_inst_5465_, 1);
lean_inc(v_toBind_5469_);
lean_dec_ref(v_inst_5465_);
v_getEnv_5470_ = lean_ctor_get(v_inst_5466_, 0);
lean_inc(v_getEnv_5470_);
lean_dec_ref(v_inst_5466_);
v_toPure_5471_ = lean_ctor_get(v_toApplicative_5468_, 1);
lean_inc(v_toPure_5471_);
lean_dec_ref(v_toApplicative_5468_);
v___x_5472_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5473_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5473_, 0, v___x_5472_);
lean_closure_set(v___f_5473_, 1, v_className_5467_);
lean_closure_set(v___f_5473_, 2, v_toPure_5471_);
v___x_5474_ = lean_apply_4(v_toBind_5469_, lean_box(0), lean_box(0), v_getEnv_5470_, v___f_5473_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5475_, lean_object* v_inst_5476_, lean_object* v_inst_5477_, lean_object* v_className_5478_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5476_, v_inst_5477_, v_className_5478_);
return v___x_5479_;
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
