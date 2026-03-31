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
size_t v_x_1570__boxed_1646_; size_t v_x_1571__boxed_1647_; lean_object* v_res_1648_; 
v_x_1570__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_x_1571__boxed_1647_ = lean_unbox_usize(v_x_1643_);
lean_dec(v_x_1643_);
v_res_1648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1641_, v_x_1570__boxed_1646_, v_x_1571__boxed_1647_, v_x_1644_, v_x_1645_);
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
lean_object* v___x_1660_; lean_object* v_mctx_1661_; lean_object* v_cache_1662_; lean_object* v_zetaDeltaFVarIds_1663_; lean_object* v_postponed_1664_; lean_object* v_diag_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1692_; 
v___x_1660_ = lean_st_ref_take(v___y_1658_);
v_mctx_1661_ = lean_ctor_get(v___x_1660_, 0);
v_cache_1662_ = lean_ctor_get(v___x_1660_, 1);
v_zetaDeltaFVarIds_1663_ = lean_ctor_get(v___x_1660_, 2);
v_postponed_1664_ = lean_ctor_get(v___x_1660_, 3);
v_diag_1665_ = lean_ctor_get(v___x_1660_, 4);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1667_ = v___x_1660_;
v_isShared_1668_ = v_isSharedCheck_1692_;
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
v_isShared_1668_ = v_isSharedCheck_1692_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_depth_1669_; lean_object* v_levelAssignDepth_1670_; lean_object* v_mvarCounter_1671_; lean_object* v_lDepth_1672_; lean_object* v_decls_1673_; lean_object* v_userNames_1674_; lean_object* v_lAssignment_1675_; lean_object* v_eAssignment_1676_; lean_object* v_dAssignment_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1691_; 
v_depth_1669_ = lean_ctor_get(v_mctx_1661_, 0);
v_levelAssignDepth_1670_ = lean_ctor_get(v_mctx_1661_, 1);
v_mvarCounter_1671_ = lean_ctor_get(v_mctx_1661_, 2);
v_lDepth_1672_ = lean_ctor_get(v_mctx_1661_, 3);
v_decls_1673_ = lean_ctor_get(v_mctx_1661_, 4);
v_userNames_1674_ = lean_ctor_get(v_mctx_1661_, 5);
v_lAssignment_1675_ = lean_ctor_get(v_mctx_1661_, 6);
v_eAssignment_1676_ = lean_ctor_get(v_mctx_1661_, 7);
v_dAssignment_1677_ = lean_ctor_get(v_mctx_1661_, 8);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_mctx_1661_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1679_ = v_mctx_1661_;
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
lean_inc(v_lDepth_1672_);
lean_inc(v_mvarCounter_1671_);
lean_inc(v_levelAssignDepth_1670_);
lean_inc(v_depth_1669_);
lean_dec(v_mctx_1661_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_eAssignment_1676_, v_mvarId_1656_, v_val_1657_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 7, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_depth_1669_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_levelAssignDepth_1670_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_mvarCounter_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_lDepth_1672_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_decls_1673_);
lean_ctor_set(v_reuseFailAlloc_1690_, 5, v_userNames_1674_);
lean_ctor_set(v_reuseFailAlloc_1690_, 6, v_lAssignment_1675_);
lean_ctor_set(v_reuseFailAlloc_1690_, 7, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 8, v_dAssignment_1677_);
v___x_1683_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1683_);
v___x_1685_ = v___x_1667_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_cache_1662_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_zetaDeltaFVarIds_1663_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_postponed_1664_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_diag_1665_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_st_ref_set(v___y_1658_, v___x_1685_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg___boxed(lean_object* v_mvarId_1693_, lean_object* v_val_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1693_, v_val_1694_, v___y_1695_);
lean_dec(v___y_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(lean_object* v_a_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = l_Lean_Expr_mvarId_x21(v_x_1699_);
v___x_1701_ = l_Lean_instBEqMVarId_beq(v___x_1700_, v_a_1698_);
lean_dec(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed(lean_object* v_a_1702_, lean_object* v_x_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(v_a_1702_, v_x_1703_);
lean_dec_ref(v_x_1703_);
lean_dec(v_a_1702_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_argMVars_1706_, lean_object* v_argVars_1707_, lean_object* v_as_1708_, size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_b_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_lt(v_i_1710_, v_sz_1709_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_b_1711_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v_a_1720_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1719_ = lean_box(0);
v_a_1720_ = lean_array_uget_borrowed(v_as_1708_, v_i_1710_);
lean_inc(v_a_1720_);
v___f_1741_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1741_, 0, v_a_1720_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = l_Array_findIdx_x3f_loop___redArg(v___f_1741_, v_argMVars_1706_, v___x_1742_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = l_Lean_instInhabitedExpr;
v___x_1746_ = lean_array_get_borrowed(v___x_1745_, v_argVars_1707_, v_val_1744_);
lean_dec(v_val_1744_);
lean_inc(v___x_1746_);
lean_inc(v_a_1720_);
v___x_1747_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_a_1720_, v___x_1746_, v___y_1713_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_dec_ref(v___x_1747_);
v___y_1722_ = v___y_1712_;
v___y_1723_ = v___y_1713_;
v___y_1724_ = v___y_1714_;
v___y_1725_ = v___y_1715_;
goto v___jp_1721_;
}
else
{
return v___x_1747_;
}
}
else
{
lean_dec(v___x_1743_);
v___y_1722_ = v___y_1712_;
v___y_1723_ = v___y_1713_;
v___y_1724_ = v___y_1714_;
v___y_1725_ = v___y_1715_;
goto v___jp_1721_;
}
v___jp_1721_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_inc(v_a_1720_);
v___x_1726_ = l_Lean_Expr_mvar___override(v_a_1720_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1724_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
v___x_1727_ = lean_infer_type(v___x_1726_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1706_, v_argVars_1707_, v_a_1728_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1729_) == 0)
{
size_t v___x_1730_; size_t v___x_1731_; 
lean_dec_ref(v___x_1729_);
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1710_, v___x_1730_);
v_i_1710_ = v___x_1731_;
v_b_1711_ = v___x_1719_;
goto _start;
}
else
{
return v___x_1729_;
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1727_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1727_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1748_, lean_object* v_argVars_1749_, lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_getMVars(v_e_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_box(0);
v_sz_1759_ = lean_array_size(v_a_1757_);
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1748_, v_argVars_1749_, v_a_1757_, v_sz_1759_, v___x_1760_, v___x_1758_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1757_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1761_, 0);
lean_dec(v_unused_1769_);
v___x_1763_ = v___x_1761_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v___x_1761_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1758_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1758_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
return v___x_1761_;
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1756_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1756_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1778_, lean_object* v_argVars_1779_, lean_object* v_e_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1778_, v_argVars_1779_, v_e_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec_ref(v_argVars_1779_);
lean_dec_ref(v_argMVars_1778_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_argMVars_1787_, lean_object* v_argVars_1788_, lean_object* v_as_1789_, lean_object* v_sz_1790_, lean_object* v_i_1791_, lean_object* v_b_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
size_t v_sz_boxed_1798_; size_t v_i_boxed_1799_; lean_object* v_res_1800_; 
v_sz_boxed_1798_ = lean_unbox_usize(v_sz_1790_);
lean_dec(v_sz_1790_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1791_);
lean_dec(v_i_1791_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1787_, v_argVars_1788_, v_as_1789_, v_sz_boxed_1798_, v_i_boxed_1799_, v_b_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v_as_1789_);
lean_dec_ref(v_argVars_1788_);
lean_dec_ref(v_argMVars_1787_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_mvarId_1801_, lean_object* v_val_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1801_, v_val_1802_, v___y_1804_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_mvarId_1809_, lean_object* v_val_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_mvarId_1809_, v_val_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_x_1818_, v_x_1819_, v_x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1822_, lean_object* v_x_1823_, size_t v_x_1824_, size_t v_x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1823_, v_x_1824_, v_x_1825_, v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
size_t v_x_1942__boxed_1835_; size_t v_x_1943__boxed_1836_; lean_object* v_res_1837_; 
v_x_1942__boxed_1835_ = lean_unbox_usize(v_x_1831_);
lean_dec(v_x_1831_);
v_x_1943__boxed_1836_ = lean_unbox_usize(v_x_1832_);
lean_dec(v_x_1832_);
v_res_1837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(v_00_u03b2_1829_, v_x_1830_, v_x_1942__boxed_1835_, v_x_1943__boxed_1836_, v_x_1833_, v_x_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1838_, lean_object* v_n_1839_, lean_object* v_k_1840_, lean_object* v_v_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1839_, v_k_1840_, v_v_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1843_, size_t v_depth_1844_, lean_object* v_keys_1845_, lean_object* v_vals_1846_, lean_object* v_heq_1847_, lean_object* v_i_1848_, lean_object* v_entries_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1844_, v_keys_1845_, v_vals_1846_, v_i_1848_, v_entries_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_depth_1852_, lean_object* v_keys_1853_, lean_object* v_vals_1854_, lean_object* v_heq_1855_, lean_object* v_i_1856_, lean_object* v_entries_1857_){
_start:
{
size_t v_depth_boxed_1858_; lean_object* v_res_1859_; 
v_depth_boxed_1858_ = lean_unbox_usize(v_depth_1852_);
lean_dec(v_depth_1852_);
v_res_1859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1851_, v_depth_boxed_1858_, v_keys_1853_, v_vals_1854_, v_heq_1855_, v_i_1856_, v_entries_1857_);
lean_dec_ref(v_vals_1854_);
lean_dec_ref(v_keys_1853_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_1861_, v_x_1862_, v_x_1863_, v_x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_Expr_hasMVar(v_e_1866_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_e_1866_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v___x_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v_cache_1877_; lean_object* v_zetaDeltaFVarIds_1878_; lean_object* v_postponed_1879_; lean_object* v_diag_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v___x_1871_ = lean_st_ref_get(v___y_1867_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_Lean_instantiateMVarsCore(v_mctx_1872_, v_e_1866_);
v_fst_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1875_);
lean_dec_ref(v___x_1873_);
v___x_1876_ = lean_st_ref_take(v___y_1867_);
v_cache_1877_ = lean_ctor_get(v___x_1876_, 1);
v_zetaDeltaFVarIds_1878_ = lean_ctor_get(v___x_1876_, 2);
v_postponed_1879_ = lean_ctor_get(v___x_1876_, 3);
v_diag_1880_ = lean_ctor_get(v___x_1876_, 4);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1876_, 0);
lean_dec(v_unused_1890_);
v___x_1882_ = v___x_1876_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_diag_1880_);
lean_inc(v_postponed_1879_);
lean_inc(v_zetaDeltaFVarIds_1878_);
lean_inc(v_cache_1877_);
lean_dec(v___x_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_snd_1875_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_snd_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_cache_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_zetaDeltaFVarIds_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_postponed_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_diag_1880_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_st_ref_set(v___y_1867_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_fst_1874_);
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1891_, v___y_1892_);
lean_dec(v___y_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1895_, v___y_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1909_, lean_object* v_opt_1910_){
_start:
{
lean_object* v_name_1911_; lean_object* v_defValue_1912_; lean_object* v_map_1913_; lean_object* v___x_1914_; 
v_name_1911_ = lean_ctor_get(v_opt_1910_, 0);
v_defValue_1912_ = lean_ctor_get(v_opt_1910_, 1);
v_map_1913_ = lean_ctor_get(v_opts_1909_, 0);
v___x_1914_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1913_, v_name_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_unbox(v_defValue_1912_);
return v___x_1915_;
}
else
{
lean_object* v_val_1916_; 
v_val_1916_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_val_1916_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v_val_1916_) == 1)
{
uint8_t v_v_1917_; 
v_v_1917_ = lean_ctor_get_uint8(v_val_1916_, 0);
lean_dec_ref(v_val_1916_);
return v_v_1917_;
}
else
{
uint8_t v___x_1918_; 
lean_dec(v_val_1916_);
v___x_1918_ = lean_unbox(v_defValue_1912_);
return v___x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1919_, lean_object* v_opt_1920_){
_start:
{
uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_res_1921_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1919_, v_opt_1920_);
lean_dec_ref(v_opt_1920_);
lean_dec_ref(v_opts_1919_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1923_, lean_object* v_as_1924_, size_t v_i_1925_, size_t v_stop_1926_){
_start:
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_usize_dec_eq(v_i_1925_, v_stop_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_array_uget_borrowed(v_as_1924_, v_i_1925_);
v___x_1929_ = lean_nat_dec_eq(v_a_1923_, v___x_1928_);
if (v___x_1929_ == 0)
{
size_t v___x_1930_; size_t v___x_1931_; 
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_add(v_i_1925_, v___x_1930_);
v_i_1925_ = v___x_1931_;
goto _start;
}
else
{
return v___x_1929_;
}
}
else
{
uint8_t v___x_1933_; 
v___x_1933_ = 0;
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1934_, lean_object* v_as_1935_, lean_object* v_i_1936_, lean_object* v_stop_1937_){
_start:
{
size_t v_i_boxed_1938_; size_t v_stop_boxed_1939_; uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_i_boxed_1938_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_stop_boxed_1939_ = lean_unbox_usize(v_stop_1937_);
lean_dec(v_stop_1937_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1934_, v_as_1935_, v_i_boxed_1938_, v_stop_boxed_1939_);
lean_dec_ref(v_as_1935_);
lean_dec(v_a_1934_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_array_get_size(v_as_1942_);
v___x_1946_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
return v___x_1946_;
}
else
{
if (v___x_1946_ == 0)
{
return v___x_1946_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1945_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1943_, v_as_1942_, v___x_1947_, v___x_1948_);
return v___x_1949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1950_, lean_object* v_a_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_as_1950_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1954_, lean_object* v_fst_1955_, lean_object* v_argVars_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, size_t v_i_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_a_1967_; uint8_t v___x_1971_; 
v___x_1971_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_b_1960_);
return v___x_1972_;
}
else
{
lean_object* v_next_1973_; 
v_next_1973_ = lean_ctor_get(v_b_1960_, 0);
lean_inc(v_next_1973_);
if (lean_obj_tag(v_next_1973_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_b_1960_);
return v___x_1974_;
}
else
{
lean_object* v_upperBound_1975_; lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2007_; 
v_upperBound_1975_ = lean_ctor_get(v_b_1960_, 1);
v_val_1976_ = lean_ctor_get(v_next_1973_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_next_1973_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1978_ = v_next_1973_;
v_isShared_1979_ = v_isSharedCheck_2007_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v_next_1973_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2007_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_nat_dec_lt(v_val_1976_, v_upperBound_1975_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_b_1960_);
return v___x_1981_;
}
else
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2004_; 
lean_inc(v_upperBound_1975_);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_b_1960_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2005_ = lean_ctor_get(v_b_1960_, 1);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_b_1960_, 0);
lean_dec(v_unused_2006_);
v___x_1983_ = v_b_1960_;
v_isShared_1984_ = v_isSharedCheck_2004_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_b_1960_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2004_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = lean_nat_add(v_val_1976_, v___x_1985_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1986_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1988_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_upperBound_1975_);
v___x_1990_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1954_, v_val_1976_);
lean_dec(v_val_1976_);
if (v___x_1991_ == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_array_uget_borrowed(v_as_1957_, v_i_1959_);
lean_inc(v_a_1992_);
v___x_1993_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1955_, v_argVars_1956_, v_a_1992_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_dec_ref(v___x_1993_);
v_a_1967_ = v___x_1990_;
goto v___jp_1966_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v___x_1990_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
v_a_1967_ = v___x_1990_;
goto v___jp_1966_;
}
}
}
}
}
}
}
}
v___jp_1966_:
{
size_t v___x_1968_; size_t v___x_1969_; 
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1959_, v___x_1968_);
v_i_1959_ = v___x_1969_;
v_b_1960_ = v_a_1967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2008_, lean_object* v_fst_2009_, lean_object* v_argVars_2010_, lean_object* v_as_2011_, lean_object* v_sz_2012_, lean_object* v_i_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
size_t v_sz_boxed_2020_; size_t v_i_boxed_2021_; lean_object* v_res_2022_; 
v_sz_boxed_2020_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2021_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2008_, v_fst_2009_, v_argVars_2010_, v_as_2011_, v_sz_boxed_2020_, v_i_boxed_2021_, v_b_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_as_2011_);
lean_dec_ref(v_argVars_2010_);
lean_dec_ref(v_fst_2009_);
lean_dec_ref(v_a_2008_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
if (lean_obj_tag(v_a_2024_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_List_reverse___redArg(v_a_2025_);
return v___x_2026_;
}
else
{
lean_object* v_head_2027_; lean_object* v_tail_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2043_; 
v_head_2027_ = lean_ctor_get(v_a_2024_, 0);
v_tail_2028_ = lean_ctor_get(v_a_2024_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2030_ = v_a_2024_;
v_isShared_2031_ = v_isSharedCheck_2043_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_tail_2028_);
lean_inc(v_head_2027_);
lean_dec(v_a_2024_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2043_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2032_ = 0;
v___x_2033_ = lean_box(v___x_2032_);
v___x_2034_ = lean_array_get(v___x_2033_, v_fst_2023_, v_head_2027_);
lean_dec(v___x_2033_);
v___x_2035_ = 3;
v___x_2036_ = lean_unbox(v___x_2034_);
lean_dec(v___x_2034_);
v___x_2037_ = l_Lean_instBEqBinderInfo_beq(v___x_2036_, v___x_2035_);
if (v___x_2037_ == 0)
{
lean_del_object(v___x_2030_);
lean_dec(v_head_2027_);
v_a_2024_ = v_tail_2028_;
goto _start;
}
else
{
lean_object* v___x_2040_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_a_2025_);
v___x_2040_ = v___x_2030_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_head_2027_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_a_2025_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_a_2024_ = v_tail_2028_;
v_a_2025_ = v___x_2040_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2044_, v_a_2045_, v_a_2046_);
lean_dec_ref(v_fst_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2048_, lean_object* v___x_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_b_2052_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_nat_dec_lt(v_a_2051_, v_upperBound_2048_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v_a_2051_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v_b_2052_);
return v___x_2055_;
}
else
{
lean_object* v_snd_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2097_; 
v_snd_2056_ = lean_ctor_get(v_b_2052_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_b_2052_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_b_2052_, 0);
lean_dec(v_unused_2098_);
v___x_2058_ = v_b_2052_;
v_isShared_2059_ = v_isSharedCheck_2097_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_snd_2056_);
lean_dec(v_b_2052_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2097_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_array_2060_; lean_object* v_start_2061_; lean_object* v_stop_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_array_2060_ = lean_ctor_get(v_snd_2056_, 0);
v_start_2061_ = lean_ctor_get(v_snd_2056_, 1);
v_stop_2062_ = lean_ctor_get(v_snd_2056_, 2);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_nat_dec_lt(v_start_2061_, v_stop_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2066_; 
lean_dec(v_a_2051_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2063_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_snd_2056_);
v___x_2066_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
else
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2093_; 
lean_inc(v_stop_2062_);
lean_inc(v_start_2061_);
lean_inc_ref(v_array_2060_);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_snd_2056_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_snd_2056_, 2);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_snd_2056_, 1);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_snd_2056_, 0);
lean_dec(v_unused_2096_);
v___x_2070_ = v_snd_2056_;
v_isShared_2071_ = v_isSharedCheck_2093_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_snd_2056_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2093_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_nat_dec_eq(v___x_2049_, v___x_2072_);
v___x_2074_ = lean_array_fget(v_array_2060_, v_start_2061_);
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_nat_add(v_start_2061_, v___x_2075_);
lean_dec(v_start_2061_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2076_);
v___x_2078_ = v___x_2070_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_array_2060_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_stop_2062_);
v___x_2078_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
uint8_t v___x_2091_; 
v___x_2091_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2050_, v_a_2051_);
if (v___x_2091_ == 0)
{
goto v___jp_2085_;
}
else
{
if (v___x_2073_ == 0)
{
lean_dec(v___x_2074_);
goto v___jp_2079_;
}
else
{
goto v___jp_2085_;
}
}
v___jp_2079_:
{
lean_object* v___x_2081_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2078_);
lean_ctor_set(v___x_2058_, 0, v___x_2063_);
v___x_2081_ = v___x_2058_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2078_);
v___x_2081_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_nat_add(v_a_2051_, v___x_2075_);
lean_dec(v_a_2051_);
v_a_2051_ = v___x_2082_;
v_b_2052_ = v___x_2081_;
goto _start;
}
}
v___jp_2085_:
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lean_Expr_hasExprMVar(v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2086_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_del_object(v___x_2058_);
lean_dec(v_a_2051_);
v___x_2087_ = lean_box(v___x_2073_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2078_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2099_, lean_object* v___x_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_b_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2099_, v___x_2100_, v_a_2101_, v_a_2102_, v_b_2103_);
lean_dec_ref(v_a_2101_);
lean_dec(v___x_2100_);
lean_dec(v_upperBound_2099_);
return v_res_2105_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2106_; lean_object* v_dummy_2107_; 
v___x_2106_ = lean_box(0);
v_dummy_2107_ = l_Lean_Expr_sort___override(v___x_2106_);
return v_dummy_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2108_, lean_object* v___x_2109_, uint8_t v___x_2110_, lean_object* v_x_2111_, lean_object* v_argTy_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
v___x_2118_ = lean_whnf(v_argTy_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_dummy_2122_; lean_object* v_nargs_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v_dummy_2122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2123_ = l_Lean_Expr_getAppNumArgs(v_a_2119_);
lean_inc(v_nargs_2123_);
v___x_2124_ = lean_mk_array(v_nargs_2123_, v_dummy_2122_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_sub(v_nargs_2123_, v___x_2125_);
lean_dec(v_nargs_2123_);
v___x_2127_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2119_, v___x_2124_, v___x_2126_);
v___x_2128_ = lean_array_get_size(v___x_2127_);
lean_inc(v___x_2108_);
v___x_2129_ = l_Array_toSubarray___redArg(v___x_2127_, v___x_2108_, v___x_2128_);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
v___x_2132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2128_, v___x_2109_, v_a_2121_, v___x_2108_, v___x_2131_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2146_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_fst_2137_; 
v_fst_2137_ = lean_ctor_get(v_a_2133_, 0);
lean_inc(v_fst_2137_);
lean_dec(v_a_2133_);
if (lean_obj_tag(v_fst_2137_) == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = lean_box(v___x_2110_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
else
{
lean_object* v_val_2142_; lean_object* v___x_2144_; 
v_val_2142_ = lean_ctor_get(v_fst_2137_, 0);
lean_inc(v_val_2142_);
lean_dec_ref(v_fst_2137_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_val_2142_);
v___x_2144_ = v___x_2135_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_val_2142_);
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
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2132_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2132_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2119_);
lean_dec(v___x_2108_);
v_a_2155_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2120_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2120_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v___x_2108_);
v_a_2163_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2118_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2118_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2171_, lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v_x_2174_, lean_object* v_argTy_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_24484__boxed_2181_; lean_object* v_res_2182_; 
v___x_24484__boxed_2181_ = lean_unbox(v___x_2173_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2171_, v___x_2172_, v___x_24484__boxed_2181_, v_x_2174_, v_argTy_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_x_2174_);
lean_dec(v___x_2172_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2186_, lean_object* v_projInfo_x3f_2187_, lean_object* v___x_2188_, lean_object* v_argVars_2189_, lean_object* v_as_2190_, size_t v_sz_2191_, size_t v_i_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_usize_dec_lt(v_i_2192_, v_sz_2191_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v___x_2188_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_b_2193_);
return v___x_2200_;
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v_b_2193_);
v_a_2201_ = lean_array_uget_borrowed(v_as_2190_, v_i_2192_);
v___x_2202_ = l_Lean_instInhabitedExpr;
v___x_2203_ = lean_array_get_borrowed(v___x_2202_, v_fst_2186_, v_a_2201_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v___x_2203_);
v___x_2204_ = lean_infer_type(v___x_2203_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2205_, v___y_2195_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2253_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2253_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2253_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2219_; lean_object* v___y_2221_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; uint8_t v___x_2238_; 
v___x_2211_ = lean_box(0);
v___x_2219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_box(v___x_2199_);
lean_inc(v___x_2188_);
v___f_2237_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2237_, 0, v___x_2235_);
lean_closure_set(v___f_2237_, 1, v___x_2188_);
lean_closure_set(v___f_2237_, 2, v___x_2236_);
v___x_2238_ = lean_nat_dec_eq(v___x_2188_, v___x_2235_);
if (lean_obj_tag(v_projInfo_x3f_2187_) == 1)
{
lean_object* v_val_2239_; lean_object* v_numParams_2240_; uint8_t v___x_2241_; 
v_val_2239_ = lean_ctor_get(v_projInfo_x3f_2187_, 0);
v_numParams_2240_ = lean_ctor_get(v_val_2239_, 1);
v___x_2241_ = lean_nat_dec_eq(v_numParams_2240_, v_a_2201_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2207_, v___f_2237_, v___x_2238_, v___x_2238_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
v___y_2221_ = v___x_2242_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2243_; 
lean_dec_ref(v___f_2237_);
lean_dec(v___x_2188_);
v___x_2243_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2186_, v_argVars_2189_, v_a_2207_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_dec_ref(v___x_2243_);
goto v___jp_2212_;
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_del_object(v___x_2209_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2207_, v___f_2237_, v___x_2238_, v___x_2238_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
v___y_2221_ = v___x_2252_;
goto v___jp_2220_;
}
v___jp_2212_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_inc(v_a_2201_);
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_a_2201_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2211_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2215_);
v___x_2217_ = v___x_2209_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
lean_object* v_a_2222_; uint8_t v___x_2223_; 
v_a_2222_ = lean_ctor_get(v___y_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___y_2221_);
v___x_2223_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
if (v___x_2223_ == 0)
{
size_t v___x_2224_; size_t v___x_2225_; 
lean_del_object(v___x_2209_);
v___x_2224_ = ((size_t)1ULL);
v___x_2225_ = lean_usize_add(v_i_2192_, v___x_2224_);
v_i_2192_ = v___x_2225_;
v_b_2193_ = v___x_2219_;
goto _start;
}
else
{
lean_dec(v___x_2188_);
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_del_object(v___x_2209_);
lean_dec(v___x_2188_);
v_a_2227_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___y_2221_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___y_2221_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v___x_2188_);
v_a_2254_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2206_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2206_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v___x_2188_);
v_a_2262_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2204_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2204_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2270_, lean_object* v_projInfo_x3f_2271_, lean_object* v___x_2272_, lean_object* v_argVars_2273_, lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
size_t v_sz_boxed_2283_; size_t v_i_boxed_2284_; lean_object* v_res_2285_; 
v_sz_boxed_2283_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2284_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2270_, v_projInfo_x3f_2271_, v___x_2272_, v_argVars_2273_, v_as_2274_, v_sz_boxed_2283_, v_i_boxed_2284_, v_b_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2274_);
lean_dec_ref(v_argVars_2273_);
lean_dec(v_projInfo_x3f_2271_);
lean_dec_ref(v_fst_2270_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v_env_2293_; lean_object* v___x_2294_; lean_object* v_mctx_2295_; lean_object* v_lctx_2296_; lean_object* v_options_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2292_ = lean_st_ref_get(v___y_2290_);
v_env_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_ref(v_env_2293_);
lean_dec(v___x_2292_);
v___x_2294_ = lean_st_ref_get(v___y_2288_);
v_mctx_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_mctx_2295_);
lean_dec(v___x_2294_);
v_lctx_2296_ = lean_ctor_get(v___y_2287_, 2);
v_options_2297_ = lean_ctor_get(v___y_2289_, 2);
lean_inc_ref(v_options_2297_);
lean_inc_ref(v_lctx_2296_);
v___x_2298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2298_, 0, v_env_2293_);
lean_ctor_set(v___x_2298_, 1, v_mctx_2295_);
lean_ctor_set(v___x_2298_, 2, v_lctx_2296_);
lean_ctor_set(v___x_2298_, 3, v_options_2297_);
v___x_2299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_msgData_2286_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_ref_2314_; lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_ref_2314_ = lean_ctor_get(v___y_2311_, 5);
v___x_2315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_inc(v_ref_2314_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v_ref_2314_);
lean_ctor_set(v___x_2320_, 1, v_a_2316_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 1);
lean_ctor_set(v___x_2318_, 0, v___x_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2332_, lean_object* v_as_2333_, size_t v_i_2334_, size_t v_stop_2335_, lean_object* v_b_2336_){
_start:
{
lean_object* v___y_2338_; uint8_t v___x_2342_; 
v___x_2342_ = lean_usize_dec_eq(v_i_2334_, v_stop_2335_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_array_uget_borrowed(v_as_2333_, v_i_2334_);
v___x_2344_ = lean_nat_dec_eq(v___x_2343_, v_next_2332_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_inc(v___x_2343_);
v___x_2345_ = lean_array_push(v_b_2336_, v___x_2343_);
v___y_2338_ = v___x_2345_;
goto v___jp_2337_;
}
else
{
v___y_2338_ = v_b_2336_;
goto v___jp_2337_;
}
}
else
{
return v_b_2336_;
}
v___jp_2337_:
{
size_t v___x_2339_; size_t v___x_2340_; 
v___x_2339_ = ((size_t)1ULL);
v___x_2340_ = lean_usize_add(v_i_2334_, v___x_2339_);
v_i_2334_ = v___x_2340_;
v_b_2336_ = v___y_2338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2346_, lean_object* v_as_2347_, lean_object* v_i_2348_, lean_object* v_stop_2349_, lean_object* v_b_2350_){
_start:
{
size_t v_i_boxed_2351_; size_t v_stop_boxed_2352_; lean_object* v_res_2353_; 
v_i_boxed_2351_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_stop_boxed_2352_ = lean_unbox_usize(v_stop_2349_);
lean_dec(v_stop_2349_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2346_, v_as_2347_, v_i_boxed_2351_, v_stop_boxed_2352_, v_b_2350_);
lean_dec_ref(v_as_2347_);
lean_dec(v_next_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2354_, size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_bs_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v___x_2363_; 
v___x_2363_ = lean_usize_dec_lt(v_i_2356_, v_sz_2355_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_bs_2357_);
return v___x_2364_;
}
else
{
lean_object* v_v_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_v_2365_ = lean_array_uget_borrowed(v_bs_2357_, v_i_2356_);
v___x_2366_ = l_Lean_instInhabitedExpr;
v___x_2367_ = lean_array_get_borrowed(v___x_2366_, v_fst_2354_, v_v_2365_);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
lean_inc(v___y_2359_);
lean_inc_ref(v___y_2358_);
lean_inc(v___x_2367_);
v___x_2368_ = lean_infer_type(v___x_2367_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2369_, v___y_2359_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; lean_object* v_bs_x27_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v_bs_x27_2373_ = lean_array_uset(v_bs_2357_, v_i_2356_, v___x_2372_);
v___x_2374_ = l_Lean_Expr_setPPExplicit(v_a_2371_, v___x_2363_);
v___x_2375_ = l_Lean_indentExpr(v___x_2374_);
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_add(v_i_2356_, v___x_2376_);
v___x_2378_ = lean_array_uset(v_bs_x27_2373_, v_i_2356_, v___x_2375_);
v_i_2356_ = v___x_2377_;
v_bs_2357_ = v___x_2378_;
goto _start;
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v_bs_2357_);
v_a_2380_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2370_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2370_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_bs_2357_);
v_a_2388_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2368_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2368_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2396_, lean_object* v_sz_2397_, lean_object* v_i_2398_, lean_object* v_bs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2396_, v_sz_boxed_2405_, v_i_boxed_2406_, v_bs_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_fst_2396_);
return v_res_2407_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2422_, lean_object* v_argVars_2423_, lean_object* v_inst_2424_, lean_object* v_a_2425_, lean_object* v_projInfo_x3f_2426_, lean_object* v_b_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v_fst_2473_; lean_object* v_snd_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2564_; 
v_fst_2473_ = lean_ctor_get(v_b_2427_, 0);
v_snd_2474_ = lean_ctor_get(v_b_2427_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_b_2427_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2476_ = v_b_2427_;
v_isShared_2477_ = v_isSharedCheck_2564_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_snd_2474_);
lean_inc(v_fst_2473_);
lean_dec(v_b_2427_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2564_;
goto v_resetjp_2475_;
}
v___jp_2433_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = l_Lean_instInhabitedExpr;
v___x_2442_ = lean_array_get_borrowed(v___x_2441_, v_fst_2422_, v___y_2436_);
lean_dec(v___y_2436_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2439_);
lean_inc(v___x_2442_);
v___x_2443_ = lean_infer_type(v___x_2442_, v___y_2439_, v___y_2437_, v___y_2435_, v___y_2438_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2422_, v_argVars_2423_, v_a_2444_, v___y_2439_, v___y_2437_, v___y_2435_, v___y_2438_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v___x_2445_);
lean_inc(v___x_2442_);
v___x_2446_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2422_, v_argVars_2423_, v___x_2442_, v___y_2439_, v___y_2437_, v___y_2435_, v___y_2438_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref(v___x_2446_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___y_2434_);
lean_ctor_set(v___x_2447_, 1, v___y_2440_);
v_b_2427_ = v___x_2447_;
goto _start;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2449_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2446_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2446_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2457_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2445_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2445_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2465_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2443_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2443_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
v_resetjp_2475_:
{
lean_object* v_next_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = lean_array_get_size(v_snd_2474_);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_nat_dec_eq(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; size_t v_sz_2545_; size_t v___x_2546_; lean_object* v___x_2547_; 
lean_del_object(v___x_2476_);
v___x_2544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2545_ = lean_array_size(v_snd_2474_);
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2422_, v_projInfo_x3f_2426_, v___x_2541_, v_argVars_2423_, v_snd_2474_, v_sz_2545_, v___x_2546_, v___x_2544_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v_fst_2549_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
v_fst_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_fst_2549_);
lean_dec(v_a_2548_);
if (lean_obj_tag(v_fst_2549_) == 0)
{
goto v___jp_2503_;
}
else
{
lean_object* v_val_2550_; 
v_val_2550_ = lean_ctor_get(v_fst_2549_, 0);
lean_inc(v_val_2550_);
lean_dec_ref(v_fst_2549_);
if (lean_obj_tag(v_val_2550_) == 0)
{
goto v___jp_2503_;
}
else
{
lean_object* v_val_2551_; 
v_val_2551_ = lean_ctor_get(v_val_2550_, 0);
lean_inc(v_val_2551_);
lean_dec_ref(v_val_2550_);
v_next_2479_ = v_val_2551_;
v___y_2480_ = v___y_2428_;
v___y_2481_ = v___y_2429_;
v___y_2482_ = v___y_2430_;
v___y_2483_ = v___y_2431_;
goto v___jp_2478_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_snd_2474_);
lean_dec(v_fst_2473_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2552_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2547_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2547_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v___x_2561_; 
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
if (v_isShared_2477_ == 0)
{
v___x_2561_ = v___x_2476_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_fst_2473_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_snd_2474_);
v___x_2561_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
v___jp_2478_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
lean_inc(v_next_2479_);
v___x_2484_ = lean_array_push(v_fst_2473_, v_next_2479_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_array_get_size(v_snd_2474_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2488_ = lean_nat_dec_lt(v___x_2485_, v___x_2486_);
if (v___x_2488_ == 0)
{
lean_dec(v_snd_2474_);
v___y_2434_ = v___x_2484_;
v___y_2435_ = v___y_2482_;
v___y_2436_ = v_next_2479_;
v___y_2437_ = v___y_2481_;
v___y_2438_ = v___y_2483_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___x_2487_;
goto v___jp_2433_;
}
else
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_nat_dec_le(v___x_2486_, v___x_2486_);
if (v___x_2489_ == 0)
{
if (v___x_2488_ == 0)
{
lean_dec(v_snd_2474_);
v___y_2434_ = v___x_2484_;
v___y_2435_ = v___y_2482_;
v___y_2436_ = v_next_2479_;
v___y_2437_ = v___y_2481_;
v___y_2438_ = v___y_2483_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___x_2487_;
goto v___jp_2433_;
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2486_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2479_, v_snd_2474_, v___x_2490_, v___x_2491_, v___x_2487_);
lean_dec(v_snd_2474_);
v___y_2434_ = v___x_2484_;
v___y_2435_ = v___y_2482_;
v___y_2436_ = v_next_2479_;
v___y_2437_ = v___y_2481_;
v___y_2438_ = v___y_2483_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___x_2492_;
goto v___jp_2433_;
}
}
else
{
size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = lean_usize_of_nat(v___x_2486_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2479_, v_snd_2474_, v___x_2493_, v___x_2494_, v___x_2487_);
lean_dec(v_snd_2474_);
v___y_2434_ = v___x_2484_;
v___y_2435_ = v___y_2482_;
v___y_2436_ = v_next_2479_;
v___y_2437_ = v___y_2481_;
v___y_2438_ = v___y_2483_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___x_2495_;
goto v___jp_2433_;
}
}
}
v___jp_2496_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = lean_array_get_borrowed(v___x_2501_, v_snd_2474_, v___x_2501_);
lean_inc(v___x_2502_);
v_next_2479_ = v___x_2502_;
v___y_2480_ = v___y_2497_;
v___y_2481_ = v___y_2498_;
v___y_2482_ = v___y_2499_;
v___y_2483_ = v___y_2500_;
goto v___jp_2478_;
}
v___jp_2503_:
{
lean_object* v_options_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_options_2504_ = lean_ctor_get(v___y_2430_, 2);
v___x_2505_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2506_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
v___y_2497_ = v___y_2428_;
v___y_2498_ = v___y_2429_;
v___y_2499_ = v___y_2430_;
v___y_2500_ = v___y_2431_;
goto v___jp_2496_;
}
else
{
size_t v_sz_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v_sz_2507_ = lean_array_size(v_snd_2474_);
v___x_2508_ = ((size_t)0ULL);
lean_inc(v_snd_2474_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2422_, v_sz_2507_, v___x_2508_, v_snd_2474_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = lean_array_to_list(v_a_2510_);
v___x_2512_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2513_ = l_Lean_MessageData_joinSep(v___x_2511_, v___x_2512_);
v___x_2514_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2424_);
v___x_2515_ = l_Lean_MessageData_ofExpr(v_inst_2424_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
lean_inc_ref(v_a_2425_);
v___x_2519_ = l_Lean_indentExpr(v_a_2425_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2513_);
v___x_2524_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2523_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref(v___x_2524_);
v___y_2497_ = v___y_2428_;
v___y_2498_ = v___y_2429_;
v___y_2499_ = v___y_2430_;
v___y_2500_ = v___y_2431_;
goto v___jp_2496_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_snd_2474_);
lean_dec(v_fst_2473_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_snd_2474_);
lean_dec(v_fst_2473_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_inst_2424_);
v_a_2533_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2509_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2509_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2565_, lean_object* v_argVars_2566_, lean_object* v_inst_2567_, lean_object* v_a_2568_, lean_object* v_projInfo_x3f_2569_, lean_object* v_b_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2565_, v_argVars_2566_, v_inst_2567_, v_a_2568_, v_projInfo_x3f_2569_, v_b_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v_projInfo_x3f_2569_);
lean_dec_ref(v_argVars_2566_);
lean_dec_ref(v_fst_2565_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2577_, size_t v_sz_2578_, size_t v_i_2579_, lean_object* v_bs_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v___x_2586_; 
v___x_2586_ = lean_usize_dec_lt(v_i_2579_, v_sz_2578_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_bs_2580_);
return v___x_2587_;
}
else
{
lean_object* v_v_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_v_2588_ = lean_array_uget_borrowed(v_bs_2580_, v_i_2579_);
v___x_2589_ = l_Lean_instInhabitedExpr;
v___x_2590_ = lean_array_get_borrowed(v___x_2589_, v_argVars_2577_, v_v_2588_);
lean_inc(v___y_2584_);
lean_inc_ref(v___y_2583_);
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
lean_inc(v___x_2590_);
v___x_2591_ = lean_infer_type(v___x_2590_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v_bs_x27_2594_; lean_object* v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v___x_2593_ = lean_unsigned_to_nat(0u);
v_bs_x27_2594_ = lean_array_uset(v_bs_2580_, v_i_2579_, v___x_2593_);
v___x_2595_ = l_Lean_indentExpr(v_a_2592_);
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_add(v_i_2579_, v___x_2596_);
v___x_2598_ = lean_array_uset(v_bs_x27_2594_, v_i_2579_, v___x_2595_);
v_i_2579_ = v___x_2597_;
v_bs_2580_ = v___x_2598_;
goto _start;
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v_bs_2580_);
v_a_2600_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2591_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2591_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2608_, lean_object* v_sz_2609_, lean_object* v_i_2610_, lean_object* v_bs_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
size_t v_sz_boxed_2617_; size_t v_i_boxed_2618_; lean_object* v_res_2619_; 
v_sz_boxed_2617_ = lean_unbox_usize(v_sz_2609_);
lean_dec(v_sz_2609_);
v_i_boxed_2618_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2608_, v_sz_boxed_2617_, v_i_boxed_2618_, v_bs_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v_argVars_2608_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
if (lean_obj_tag(v_a_2620_) == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = l_List_reverse___redArg(v_a_2621_);
return v___x_2622_;
}
else
{
lean_object* v_head_2623_; lean_object* v_tail_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2635_; 
v_head_2623_ = lean_ctor_get(v_a_2620_, 0);
v_tail_2624_ = lean_ctor_get(v_a_2620_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2626_ = v_a_2620_;
v_isShared_2627_ = v_isSharedCheck_2635_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_tail_2624_);
lean_inc(v_head_2623_);
lean_dec(v_a_2620_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2635_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2628_ = l_Nat_reprFast(v_head_2623_);
v___x_2629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = l_Lean_MessageData_ofFormat(v___x_2629_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v_a_2621_);
lean_ctor_set(v___x_2626_, 0, v___x_2630_);
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_a_2621_);
v___x_2632_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v_a_2620_ = v_tail_2624_;
v_a_2621_ = v___x_2632_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2636_; double v___x_2637_; 
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_float_of_nat(v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2640_, lean_object* v_msg_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_ref_2647_; lean_object* v___x_2648_; lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2693_; 
v_ref_2647_ = lean_ctor_get(v___y_2644_, 5);
v___x_2648_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2693_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2693_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v_traceState_2654_; lean_object* v_env_2655_; lean_object* v_nextMacroScope_2656_; lean_object* v_ngen_2657_; lean_object* v_auxDeclNGen_2658_; lean_object* v_cache_2659_; lean_object* v_messages_2660_; lean_object* v_infoState_2661_; lean_object* v_snapshotTasks_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2692_; 
v___x_2653_ = lean_st_ref_take(v___y_2645_);
v_traceState_2654_ = lean_ctor_get(v___x_2653_, 4);
v_env_2655_ = lean_ctor_get(v___x_2653_, 0);
v_nextMacroScope_2656_ = lean_ctor_get(v___x_2653_, 1);
v_ngen_2657_ = lean_ctor_get(v___x_2653_, 2);
v_auxDeclNGen_2658_ = lean_ctor_get(v___x_2653_, 3);
v_cache_2659_ = lean_ctor_get(v___x_2653_, 5);
v_messages_2660_ = lean_ctor_get(v___x_2653_, 6);
v_infoState_2661_ = lean_ctor_get(v___x_2653_, 7);
v_snapshotTasks_2662_ = lean_ctor_get(v___x_2653_, 8);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2664_ = v___x_2653_;
v_isShared_2665_ = v_isSharedCheck_2692_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snapshotTasks_2662_);
lean_inc(v_infoState_2661_);
lean_inc(v_messages_2660_);
lean_inc(v_cache_2659_);
lean_inc(v_traceState_2654_);
lean_inc(v_auxDeclNGen_2658_);
lean_inc(v_ngen_2657_);
lean_inc(v_nextMacroScope_2656_);
lean_inc(v_env_2655_);
lean_dec(v___x_2653_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2692_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
uint64_t v_tid_2666_; lean_object* v_traces_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2691_; 
v_tid_2666_ = lean_ctor_get_uint64(v_traceState_2654_, sizeof(void*)*1);
v_traces_2667_ = lean_ctor_get(v_traceState_2654_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_traceState_2654_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2669_ = v_traceState_2654_;
v_isShared_2670_ = v_isSharedCheck_2691_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_traces_2667_);
lean_dec(v_traceState_2654_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2691_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; double v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2671_ = lean_box(0);
v___x_2672_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2673_ = 0;
v___x_2674_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2675_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2675_, 0, v_cls_2640_);
lean_ctor_set(v___x_2675_, 1, v___x_2671_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
lean_ctor_set_float(v___x_2675_, sizeof(void*)*3, v___x_2672_);
lean_ctor_set_float(v___x_2675_, sizeof(void*)*3 + 8, v___x_2672_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*3 + 16, v___x_2673_);
v___x_2676_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2677_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v_a_2649_);
lean_ctor_set(v___x_2677_, 2, v___x_2676_);
lean_inc(v_ref_2647_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_ref_2647_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_PersistentArray_push___redArg(v_traces_2667_, v___x_2678_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2679_);
v___x_2681_ = v___x_2669_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2679_);
lean_ctor_set_uint64(v_reuseFailAlloc_2690_, sizeof(void*)*1, v_tid_2666_);
v___x_2681_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2683_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 4, v___x_2681_);
v___x_2683_ = v___x_2664_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_env_2655_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_nextMacroScope_2656_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v_ngen_2657_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_auxDeclNGen_2658_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2689_, 5, v_cache_2659_);
lean_ctor_set(v_reuseFailAlloc_2689_, 6, v_messages_2660_);
lean_ctor_set(v_reuseFailAlloc_2689_, 7, v_infoState_2661_);
lean_ctor_set(v_reuseFailAlloc_2689_, 8, v_snapshotTasks_2662_);
v___x_2683_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_st_ref_set(v___y_2645_, v___x_2683_);
v___x_2685_ = lean_box(0);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2685_);
v___x_2687_ = v___x_2651_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2694_, lean_object* v_msg_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2694_, v_msg_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2711_ = l_Lean_Name_append(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2724_, lean_object* v_fst_2725_, lean_object* v_fst_2726_, lean_object* v_inst_2727_, lean_object* v_a_2728_, lean_object* v_projInfo_x3f_2729_, lean_object* v_argVars_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2724_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v_dummy_2739_; lean_object* v_nargs_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v___x_2737_);
v_dummy_2739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2740_ = l_Lean_Expr_getAppNumArgs(v_a_2724_);
lean_inc(v_nargs_2740_);
v___x_2741_ = lean_mk_array(v_nargs_2740_, v_dummy_2739_);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_sub(v_nargs_2740_, v___x_2742_);
lean_dec(v_nargs_2740_);
lean_inc_ref(v_a_2724_);
v___x_2744_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2724_, v___x_2741_, v___x_2743_);
v___x_2745_ = lean_array_get_size(v___x_2744_);
v___x_2746_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
lean_ctor_set(v___x_2747_, 1, v___x_2745_);
v_sz_2748_ = lean_array_size(v___x_2744_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2738_, v_fst_2725_, v_argVars_2730_, v___x_2744_, v_sz_2748_, v___x_2749_, v___x_2747_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec_ref(v___x_2744_);
lean_dec(v_a_2738_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec_ref(v___x_2750_);
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2752_ = lean_array_get_size(v_fst_2725_);
v___x_2753_ = l_List_range(v___x_2752_);
v___x_2754_ = lean_box(0);
v___x_2755_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2726_, v___x_2753_, v___x_2754_);
v___x_2756_ = lean_array_mk(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2751_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_inc_ref(v_inst_2727_);
v___x_2758_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2725_, v_argVars_2730_, v_inst_2727_, v_a_2728_, v_projInfo_x3f_2729_, v___x_2757_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2851_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2851_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2851_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_fst_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2849_; 
v_fst_2763_ = lean_ctor_get(v_a_2759_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_a_2759_, 1);
lean_dec(v_unused_2850_);
v___x_2765_ = v_a_2759_;
v_isShared_2766_ = v_isSharedCheck_2849_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_fst_2763_);
lean_dec(v_a_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2849_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v_options_2771_; lean_object* v_inheritedTraceOptions_2772_; lean_object* v___y_2773_; lean_object* v_options_2829_; lean_object* v_inheritedTraceOptions_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v_options_2829_ = lean_ctor_get(v___y_2734_, 2);
v_inheritedTraceOptions_2830_ = lean_ctor_get(v___y_2734_, 13);
v___x_2831_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2832_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2829_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_dec_ref(v_a_2724_);
v___y_2768_ = v___y_2732_;
v___y_2769_ = v___y_2733_;
v___y_2770_ = v___y_2734_;
v_options_2771_ = v_options_2829_;
v_inheritedTraceOptions_2772_ = v_inheritedTraceOptions_2830_;
v___y_2773_ = v___y_2735_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2833_; lean_object* v_a_2834_; uint8_t v___x_2835_; 
v___x_2833_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2724_, v___y_2733_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref(v___x_2833_);
v___x_2835_ = l_Lean_Expr_hasExprMVar(v_a_2834_);
if (v___x_2835_ == 0)
{
lean_dec(v_a_2834_);
v___y_2768_ = v___y_2732_;
v___y_2769_ = v___y_2733_;
v___y_2770_ = v___y_2734_;
v_options_2771_ = v_options_2829_;
v_inheritedTraceOptions_2772_ = v_inheritedTraceOptions_2830_;
v___y_2773_ = v___y_2735_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2761_);
lean_dec_ref(v_inst_2727_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2837_ = l_Lean_Expr_setPPExplicit(v_a_2834_, v___x_2835_);
v___x_2838_ = l_Lean_indentExpr(v___x_2837_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2836_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2839_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
v___jp_2767_:
{
uint8_t v_hasTrace_2774_; 
v_hasTrace_2774_ = lean_ctor_get_uint8(v_options_2771_, sizeof(void*)*1);
if (v_hasTrace_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_del_object(v___x_2765_);
lean_dec_ref(v_inst_2727_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_fst_2763_);
v___x_2776_ = v___x_2761_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_fst_2763_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2772_, v_options_2771_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; 
lean_del_object(v___x_2765_);
lean_dec_ref(v_inst_2727_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_fst_2763_);
v___x_2782_ = v___x_2761_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_fst_2763_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
size_t v_sz_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2761_);
v_sz_2784_ = lean_array_size(v_fst_2763_);
lean_inc(v_fst_2763_);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2730_, v_sz_2784_, v___x_2749_, v_fst_2763_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2773_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2788_ = l_Lean_MessageData_ofExpr(v_inst_2727_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 7);
lean_ctor_set(v___x_2765_, 1, v___x_2788_);
lean_ctor_set(v___x_2765_, 0, v___x_2787_);
v___x_2790_ = v___x_2765_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2791_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
lean_inc(v_fst_2763_);
v___x_2793_ = lean_array_to_list(v_fst_2763_);
v___x_2794_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2793_, v___x_2754_);
v___x_2795_ = l_Lean_MessageData_ofList(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_array_to_list(v_a_2786_);
v___x_2800_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2801_ = l_Lean_MessageData_joinSep(v___x_2799_, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2798_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2778_, v___x_2802_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2773_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v___x_2803_, 0);
lean_dec(v_unused_2811_);
v___x_2805_ = v___x_2803_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_dec(v___x_2803_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_fst_2763_);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_fst_2763_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_fst_2763_);
v_a_2812_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2803_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2803_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_dec_ref(v_inst_2727_);
v_a_2821_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2785_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2785_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
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
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v_inst_2727_);
lean_dec_ref(v_a_2724_);
v_a_2852_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2758_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2758_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_a_2728_);
lean_dec_ref(v_inst_2727_);
lean_dec_ref(v_a_2724_);
v_a_2860_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2750_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2750_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_dec_ref(v_a_2728_);
lean_dec_ref(v_inst_2727_);
lean_dec_ref(v_a_2724_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2868_, lean_object* v_fst_2869_, lean_object* v_fst_2870_, lean_object* v_inst_2871_, lean_object* v_a_2872_, lean_object* v_projInfo_x3f_2873_, lean_object* v_argVars_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2868_, v_fst_2869_, v_fst_2870_, v_inst_2871_, v_a_2872_, v_projInfo_x3f_2873_, v_argVars_2874_, v_x_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_x_2875_);
lean_dec_ref(v_argVars_2874_);
lean_dec(v_projInfo_x3f_2873_);
lean_dec_ref(v_fst_2870_);
lean_dec_ref(v_fst_2869_);
return v_res_2881_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2882_; uint64_t v___x_2883_; 
v___x_2882_ = 2;
v___x_2883_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2884_, lean_object* v_projInfo_x3f_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; uint8_t v_foApprox_2892_; uint8_t v_ctxApprox_2893_; uint8_t v_quasiPatternApprox_2894_; uint8_t v_constApprox_2895_; uint8_t v_isDefEqStuckEx_2896_; uint8_t v_unificationHints_2897_; uint8_t v_proofIrrelevance_2898_; uint8_t v_assignSyntheticOpaque_2899_; uint8_t v_offsetCnstrs_2900_; uint8_t v_etaStruct_2901_; uint8_t v_univApprox_2902_; uint8_t v_iota_2903_; uint8_t v_beta_2904_; uint8_t v_proj_2905_; uint8_t v_zeta_2906_; uint8_t v_zetaDelta_2907_; uint8_t v_zetaUnused_2908_; uint8_t v_zetaHave_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2974_; 
v___x_2891_ = l_Lean_Meta_Context_config(v_a_2886_);
v_foApprox_2892_ = lean_ctor_get_uint8(v___x_2891_, 0);
v_ctxApprox_2893_ = lean_ctor_get_uint8(v___x_2891_, 1);
v_quasiPatternApprox_2894_ = lean_ctor_get_uint8(v___x_2891_, 2);
v_constApprox_2895_ = lean_ctor_get_uint8(v___x_2891_, 3);
v_isDefEqStuckEx_2896_ = lean_ctor_get_uint8(v___x_2891_, 4);
v_unificationHints_2897_ = lean_ctor_get_uint8(v___x_2891_, 5);
v_proofIrrelevance_2898_ = lean_ctor_get_uint8(v___x_2891_, 6);
v_assignSyntheticOpaque_2899_ = lean_ctor_get_uint8(v___x_2891_, 7);
v_offsetCnstrs_2900_ = lean_ctor_get_uint8(v___x_2891_, 8);
v_etaStruct_2901_ = lean_ctor_get_uint8(v___x_2891_, 10);
v_univApprox_2902_ = lean_ctor_get_uint8(v___x_2891_, 11);
v_iota_2903_ = lean_ctor_get_uint8(v___x_2891_, 12);
v_beta_2904_ = lean_ctor_get_uint8(v___x_2891_, 13);
v_proj_2905_ = lean_ctor_get_uint8(v___x_2891_, 14);
v_zeta_2906_ = lean_ctor_get_uint8(v___x_2891_, 15);
v_zetaDelta_2907_ = lean_ctor_get_uint8(v___x_2891_, 16);
v_zetaUnused_2908_ = lean_ctor_get_uint8(v___x_2891_, 17);
v_zetaHave_2909_ = lean_ctor_get_uint8(v___x_2891_, 18);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2911_ = v___x_2891_;
v_isShared_2912_ = v_isSharedCheck_2974_;
goto v_resetjp_2910_;
}
else
{
lean_dec(v___x_2891_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2974_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
uint8_t v_trackZetaDelta_2913_; lean_object* v_zetaDeltaSet_2914_; lean_object* v_lctx_2915_; lean_object* v_localInstances_2916_; lean_object* v_defEqCtx_x3f_2917_; lean_object* v_synthPendingDepth_2918_; lean_object* v_canUnfold_x3f_2919_; uint8_t v_univApprox_2920_; uint8_t v_inTypeClassResolution_2921_; uint8_t v_cacheInferType_2922_; uint8_t v___x_2923_; lean_object* v_config_2925_; 
v_trackZetaDelta_2913_ = lean_ctor_get_uint8(v_a_2886_, sizeof(void*)*7);
v_zetaDeltaSet_2914_ = lean_ctor_get(v_a_2886_, 1);
v_lctx_2915_ = lean_ctor_get(v_a_2886_, 2);
v_localInstances_2916_ = lean_ctor_get(v_a_2886_, 3);
v_defEqCtx_x3f_2917_ = lean_ctor_get(v_a_2886_, 4);
v_synthPendingDepth_2918_ = lean_ctor_get(v_a_2886_, 5);
v_canUnfold_x3f_2919_ = lean_ctor_get(v_a_2886_, 6);
v_univApprox_2920_ = lean_ctor_get_uint8(v_a_2886_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2921_ = lean_ctor_get_uint8(v_a_2886_, sizeof(void*)*7 + 2);
v_cacheInferType_2922_ = lean_ctor_get_uint8(v_a_2886_, sizeof(void*)*7 + 3);
v___x_2923_ = 2;
if (v_isShared_2912_ == 0)
{
v_config_2925_ = v___x_2911_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 0, v_foApprox_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 1, v_ctxApprox_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 2, v_quasiPatternApprox_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 3, v_constApprox_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 4, v_isDefEqStuckEx_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 5, v_unificationHints_2897_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 6, v_proofIrrelevance_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 7, v_assignSyntheticOpaque_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 8, v_offsetCnstrs_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 10, v_etaStruct_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 11, v_univApprox_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 12, v_iota_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 13, v_beta_2904_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 14, v_proj_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 15, v_zeta_2906_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 16, v_zetaDelta_2907_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 17, v_zetaUnused_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, 18, v_zetaHave_2909_);
v_config_2925_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
uint64_t v___x_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v___x_2929_; uint64_t v___x_2930_; uint64_t v_key_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_ctor_set_uint8(v_config_2925_, 9, v___x_2923_);
v___x_2926_ = l_Lean_Meta_Context_configKey(v_a_2886_);
v___x_2927_ = 2ULL;
v___x_2928_ = lean_uint64_shift_right(v___x_2926_, v___x_2927_);
v___x_2929_ = lean_uint64_shift_left(v___x_2928_, v___x_2927_);
v___x_2930_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2931_ = lean_uint64_lor(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2932_, 0, v_config_2925_);
lean_ctor_set_uint64(v___x_2932_, sizeof(void*)*1, v_key_2931_);
lean_inc(v_canUnfold_x3f_2919_);
lean_inc(v_synthPendingDepth_2918_);
lean_inc(v_defEqCtx_x3f_2917_);
lean_inc_ref(v_localInstances_2916_);
lean_inc_ref(v_lctx_2915_);
lean_inc(v_zetaDeltaSet_2914_);
v___x_2933_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v_zetaDeltaSet_2914_);
lean_ctor_set(v___x_2933_, 2, v_lctx_2915_);
lean_ctor_set(v___x_2933_, 3, v_localInstances_2916_);
lean_ctor_set(v___x_2933_, 4, v_defEqCtx_x3f_2917_);
lean_ctor_set(v___x_2933_, 5, v_synthPendingDepth_2918_);
lean_ctor_set(v___x_2933_, 6, v_canUnfold_x3f_2919_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7, v_trackZetaDelta_2913_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 1, v_univApprox_2920_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2921_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 3, v_cacheInferType_2922_);
lean_inc(v_a_2889_);
lean_inc_ref(v_a_2888_);
lean_inc(v_a_2887_);
lean_inc_ref(v___x_2933_);
lean_inc_ref(v_inst_2884_);
v___x_2934_ = lean_infer_type(v_inst_2884_, v___x_2933_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_n(v_a_2935_, 2);
lean_dec_ref(v___x_2934_);
v___x_2936_ = lean_box(0);
v___x_2937_ = 0;
v___x_2938_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2935_, v___x_2936_, v___x_2937_, v___x_2933_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v_snd_2940_; lean_object* v_fst_2941_; lean_object* v_fst_2942_; lean_object* v_snd_2943_; lean_object* v___x_2944_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v_snd_2940_ = lean_ctor_get(v_a_2939_, 1);
lean_inc(v_snd_2940_);
v_fst_2941_ = lean_ctor_get(v_a_2939_, 0);
lean_inc(v_fst_2941_);
lean_dec(v_a_2939_);
v_fst_2942_ = lean_ctor_get(v_snd_2940_, 0);
lean_inc(v_fst_2942_);
v_snd_2943_ = lean_ctor_get(v_snd_2940_, 1);
lean_inc(v_snd_2943_);
lean_dec(v_snd_2940_);
lean_inc(v_a_2889_);
lean_inc_ref(v_a_2888_);
lean_inc(v_a_2887_);
lean_inc_ref(v___x_2933_);
v___x_2944_ = lean_whnf(v_snd_2943_, v___x_2933_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___f_2946_; uint8_t v___x_2947_; lean_object* v___x_2948_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
lean_inc(v_a_2935_);
v___f_2946_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2946_, 0, v_a_2945_);
lean_closure_set(v___f_2946_, 1, v_fst_2941_);
lean_closure_set(v___f_2946_, 2, v_fst_2942_);
lean_closure_set(v___f_2946_, 3, v_inst_2884_);
lean_closure_set(v___f_2946_, 4, v_a_2935_);
lean_closure_set(v___f_2946_, 5, v_projInfo_x3f_2885_);
v___x_2947_ = 0;
v___x_2948_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2935_, v___f_2946_, v___x_2947_, v___x_2947_, v___x_2933_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec_ref(v___x_2933_);
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_fst_2942_);
lean_dec(v_fst_2941_);
lean_dec(v_a_2935_);
lean_dec_ref(v___x_2933_);
lean_dec(v_projInfo_x3f_2885_);
lean_dec_ref(v_inst_2884_);
v_a_2949_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2944_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2944_);
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
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_a_2935_);
lean_dec_ref(v___x_2933_);
lean_dec(v_projInfo_x3f_2885_);
lean_dec_ref(v_inst_2884_);
v_a_2957_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2938_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2938_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v___x_2933_);
lean_dec(v_projInfo_x3f_2885_);
lean_dec_ref(v_inst_2884_);
v_a_2965_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2934_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2934_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_2975_, lean_object* v_projInfo_x3f_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_2975_, v_projInfo_x3f_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_2983_, lean_object* v___x_2984_, lean_object* v_a_2985_, lean_object* v_inst_2986_, lean_object* v_R_2987_, lean_object* v_a_2988_, lean_object* v_b_2989_, lean_object* v_c_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2983_, v___x_2984_, v_a_2985_, v_a_2988_, v_b_2989_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_2997_, lean_object* v___x_2998_, lean_object* v_a_2999_, lean_object* v_inst_3000_, lean_object* v_R_3001_, lean_object* v_a_3002_, lean_object* v_b_3003_, lean_object* v_c_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_2997_, v___x_2998_, v_a_2999_, v_inst_3000_, v_R_3001_, v_a_3002_, v_b_3003_, v_c_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v_a_2999_);
lean_dec(v___x_2998_);
lean_dec(v_upperBound_2997_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3019_, lean_object* v_msg_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3019_, v_msg_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; lean_object* v_env_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3030_ = lean_st_ref_get(v___y_3028_);
v_env_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc_ref(v_env_3031_);
lean_dec(v___x_3030_);
v___x_3032_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3031_, v_declName_3027_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3034_, v___y_3035_);
lean_dec(v___y_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3038_, v___y_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3051_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3058_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
lean_ctor_set(v___x_3058_, 3, v___x_3057_);
lean_ctor_set(v___x_3058_, 4, v___x_3057_);
lean_ctor_set(v___x_3058_, 5, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3059_, lean_object* v_b_3060_, uint8_t v_kind_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_currNamespace_3066_; lean_object* v___x_3067_; lean_object* v_env_3068_; lean_object* v_nextMacroScope_3069_; lean_object* v_ngen_3070_; lean_object* v_auxDeclNGen_3071_; lean_object* v_traceState_3072_; lean_object* v_messages_3073_; lean_object* v_infoState_3074_; lean_object* v_snapshotTasks_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3102_; 
v_currNamespace_3066_ = lean_ctor_get(v___y_3063_, 6);
v___x_3067_ = lean_st_ref_take(v___y_3064_);
v_env_3068_ = lean_ctor_get(v___x_3067_, 0);
v_nextMacroScope_3069_ = lean_ctor_get(v___x_3067_, 1);
v_ngen_3070_ = lean_ctor_get(v___x_3067_, 2);
v_auxDeclNGen_3071_ = lean_ctor_get(v___x_3067_, 3);
v_traceState_3072_ = lean_ctor_get(v___x_3067_, 4);
v_messages_3073_ = lean_ctor_get(v___x_3067_, 6);
v_infoState_3074_ = lean_ctor_get(v___x_3067_, 7);
v_snapshotTasks_3075_ = lean_ctor_get(v___x_3067_, 8);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3067_, 5);
lean_dec(v_unused_3103_);
v___x_3077_ = v___x_3067_;
v_isShared_3078_ = v_isSharedCheck_3102_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_snapshotTasks_3075_);
lean_inc(v_infoState_3074_);
lean_inc(v_messages_3073_);
lean_inc(v_traceState_3072_);
lean_inc(v_auxDeclNGen_3071_);
lean_inc(v_ngen_3070_);
lean_inc(v_nextMacroScope_3069_);
lean_inc(v_env_3068_);
lean_dec(v___x_3067_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3102_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
lean_inc(v_currNamespace_3066_);
v___x_3079_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3068_, v_ext_3059_, v_b_3060_, v_kind_3061_, v_currNamespace_3066_);
v___x_3080_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 5, v___x_3080_);
lean_ctor_set(v___x_3077_, 0, v___x_3079_);
v___x_3082_ = v___x_3077_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_nextMacroScope_3069_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_ngen_3070_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_auxDeclNGen_3071_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v_traceState_3072_);
lean_ctor_set(v_reuseFailAlloc_3101_, 5, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3101_, 6, v_messages_3073_);
lean_ctor_set(v_reuseFailAlloc_3101_, 7, v_infoState_3074_);
lean_ctor_set(v_reuseFailAlloc_3101_, 8, v_snapshotTasks_3075_);
v___x_3082_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_mctx_3085_; lean_object* v_zetaDeltaFVarIds_3086_; lean_object* v_postponed_3087_; lean_object* v_diag_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3099_; 
v___x_3083_ = lean_st_ref_set(v___y_3064_, v___x_3082_);
v___x_3084_ = lean_st_ref_take(v___y_3062_);
v_mctx_3085_ = lean_ctor_get(v___x_3084_, 0);
v_zetaDeltaFVarIds_3086_ = lean_ctor_get(v___x_3084_, 2);
v_postponed_3087_ = lean_ctor_get(v___x_3084_, 3);
v_diag_3088_ = lean_ctor_get(v___x_3084_, 4);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3084_, 1);
lean_dec(v_unused_3100_);
v___x_3090_ = v___x_3084_;
v_isShared_3091_ = v_isSharedCheck_3099_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_diag_3088_);
lean_inc(v_postponed_3087_);
lean_inc(v_zetaDeltaFVarIds_3086_);
lean_inc(v_mctx_3085_);
lean_dec(v___x_3084_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3099_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 1, v___x_3092_);
v___x_3094_ = v___x_3090_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_mctx_3085_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_zetaDeltaFVarIds_3086_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_postponed_3087_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_diag_3088_);
v___x_3094_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_st_ref_set(v___y_3062_, v___x_3094_);
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3104_, lean_object* v_b_3105_, lean_object* v_kind_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v_kind_boxed_3111_; lean_object* v_res_3112_; 
v_kind_boxed_3111_ = lean_unbox(v_kind_3106_);
v_res_3112_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3104_, v_b_3105_, v_kind_boxed_3111_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_00_u03c3_3115_, lean_object* v_ext_3116_, lean_object* v_b_3117_, uint8_t v_kind_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3116_, v_b_3117_, v_kind_3118_, v___y_3120_, v___y_3121_, v___y_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_00_u03b2_3126_, lean_object* v_00_u03c3_3127_, lean_object* v_ext_3128_, lean_object* v_b_3129_, lean_object* v_kind_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
uint8_t v_kind_boxed_3136_; lean_object* v_res_3137_; 
v_kind_boxed_3136_ = lean_unbox(v_kind_3130_);
v_res_3137_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3125_, v_00_u03b2_3126_, v_00_u03c3_3127_, v_ext_3128_, v_b_3129_, v_kind_boxed_3136_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; lean_object* v_env_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3141_ = lean_st_ref_get(v___y_3139_);
v_env_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_ref(v_env_3142_);
lean_dec(v___x_3141_);
v___x_3143_ = lean_get_reducibility_status(v_env_3142_, v_declName_3138_);
v___x_3144_ = lean_box(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3146_, v___y_3147_);
lean_dec(v___y_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3150_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
return v_res_3163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
lean_ctor_set(v___x_3169_, 2, v___x_3168_);
lean_ctor_set(v___x_3169_, 3, v___x_3167_);
lean_ctor_set(v___x_3169_, 4, v___x_3167_);
lean_ctor_set(v___x_3169_, 5, v___x_3167_);
lean_ctor_set(v___x_3169_, 6, v___x_3167_);
lean_ctor_set(v___x_3169_, 7, v___x_3167_);
lean_ctor_set(v___x_3169_, 8, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_unsigned_to_nat(32u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3173_ = ((size_t)5ULL);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_unsigned_to_nat(32u);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_3175_);
v___x_3177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3178_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___x_3176_);
lean_ctor_set(v___x_3178_, 2, v___x_3174_);
lean_ctor_set(v___x_3178_, 3, v___x_3174_);
lean_ctor_set_usize(v___x_3178_, 4, v___x_3173_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3179_ = lean_box(1);
v___x_3180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3180_);
lean_ctor_set(v___x_3182_, 2, v___x_3179_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3204_, lean_object* v_declHint_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; lean_object* v_env_3209_; uint8_t v___x_3210_; 
v___x_3208_ = lean_st_ref_get(v___y_3206_);
v_env_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_ref(v_env_3209_);
lean_dec(v___x_3208_);
v___x_3210_ = l_Lean_Name_isAnonymous(v_declHint_3205_);
if (v___x_3210_ == 0)
{
uint8_t v_isExporting_3211_; 
v_isExporting_3211_ = lean_ctor_get_uint8(v_env_3209_, sizeof(void*)*8);
if (v_isExporting_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v_env_3209_);
lean_dec(v_declHint_3205_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_msg_3204_);
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
lean_inc_ref(v_env_3209_);
v___x_3213_ = l_Lean_Environment_setExporting(v_env_3209_, v___x_3210_);
lean_inc(v_declHint_3205_);
lean_inc_ref(v___x_3213_);
v___x_3214_ = l_Lean_Environment_contains(v___x_3213_, v_declHint_3205_, v_isExporting_3211_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; 
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_env_3209_);
lean_dec(v_declHint_3205_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_msg_3204_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v_c_3221_; lean_object* v___x_3222_; 
v___x_3216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3218_ = l_Lean_Options_empty;
v___x_3219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3213_);
lean_ctor_set(v___x_3219_, 1, v___x_3216_);
lean_ctor_set(v___x_3219_, 2, v___x_3217_);
lean_ctor_set(v___x_3219_, 3, v___x_3218_);
lean_inc(v_declHint_3205_);
v___x_3220_ = l_Lean_MessageData_ofConstName(v_declHint_3205_, v___x_3210_);
v_c_3221_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3221_, 0, v___x_3219_);
lean_ctor_set(v_c_3221_, 1, v___x_3220_);
v___x_3222_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3209_, v_declHint_3205_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec_ref(v_env_3209_);
lean_dec(v_declHint_3205_);
v___x_3223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v_c_3221_);
v___x_3225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = l_Lean_MessageData_note(v___x_3226_);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_msg_3204_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
else
{
lean_object* v_val_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3265_; 
v_val_3230_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3232_ = v___x_3222_;
v_isShared_3233_ = v_isSharedCheck_3265_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_val_3230_);
lean_dec(v___x_3222_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3265_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_mod_3237_; uint8_t v___x_3238_; 
v___x_3234_ = lean_box(0);
v___x_3235_ = l_Lean_Environment_header(v_env_3209_);
lean_dec_ref(v_env_3209_);
v___x_3236_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3235_);
v_mod_3237_ = lean_array_get(v___x_3234_, v___x_3236_, v_val_3230_);
lean_dec(v_val_3230_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = l_Lean_isPrivateName(v_declHint_3205_);
lean_dec(v_declHint_3205_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v_c_3221_);
v___x_3241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_MessageData_ofName(v_mod_3237_);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_MessageData_note(v___x_3246_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_msg_3204_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3248_);
v___x_3250_ = v___x_3232_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
lean_ctor_set(v___x_3253_, 1, v_c_3221_);
v___x_3254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_MessageData_ofName(v_mod_3237_);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_MessageData_note(v___x_3259_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_msg_3204_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3261_);
v___x_3263_ = v___x_3232_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
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
}
}
}
else
{
lean_object* v___x_3266_; 
lean_dec_ref(v_env_3209_);
lean_dec(v_declHint_3205_);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_msg_3204_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3267_, lean_object* v_declHint_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3267_, v_declHint_3268_, v___y_3269_);
lean_dec(v___y_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3272_, lean_object* v_declHint_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3289_; 
v___x_3279_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3272_, v_declHint_3273_, v___y_3277_);
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3284_ = l_Lean_unknownIdentifierMessageTag;
v___x_3285_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_a_3280_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3285_);
v___x_3287_ = v___x_3282_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3290_, lean_object* v_declHint_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3290_, v_declHint_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3298_, lean_object* v_msg_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_fileName_3305_; lean_object* v_fileMap_3306_; lean_object* v_options_3307_; lean_object* v_currRecDepth_3308_; lean_object* v_maxRecDepth_3309_; lean_object* v_ref_3310_; lean_object* v_currNamespace_3311_; lean_object* v_openDecls_3312_; lean_object* v_initHeartbeats_3313_; lean_object* v_maxHeartbeats_3314_; lean_object* v_quotContext_3315_; lean_object* v_currMacroScope_3316_; uint8_t v_diag_3317_; lean_object* v_cancelTk_x3f_3318_; uint8_t v_suppressElabErrors_3319_; lean_object* v_inheritedTraceOptions_3320_; lean_object* v_ref_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_fileName_3305_ = lean_ctor_get(v___y_3302_, 0);
v_fileMap_3306_ = lean_ctor_get(v___y_3302_, 1);
v_options_3307_ = lean_ctor_get(v___y_3302_, 2);
v_currRecDepth_3308_ = lean_ctor_get(v___y_3302_, 3);
v_maxRecDepth_3309_ = lean_ctor_get(v___y_3302_, 4);
v_ref_3310_ = lean_ctor_get(v___y_3302_, 5);
v_currNamespace_3311_ = lean_ctor_get(v___y_3302_, 6);
v_openDecls_3312_ = lean_ctor_get(v___y_3302_, 7);
v_initHeartbeats_3313_ = lean_ctor_get(v___y_3302_, 8);
v_maxHeartbeats_3314_ = lean_ctor_get(v___y_3302_, 9);
v_quotContext_3315_ = lean_ctor_get(v___y_3302_, 10);
v_currMacroScope_3316_ = lean_ctor_get(v___y_3302_, 11);
v_diag_3317_ = lean_ctor_get_uint8(v___y_3302_, sizeof(void*)*14);
v_cancelTk_x3f_3318_ = lean_ctor_get(v___y_3302_, 12);
v_suppressElabErrors_3319_ = lean_ctor_get_uint8(v___y_3302_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3320_ = lean_ctor_get(v___y_3302_, 13);
v_ref_3321_ = l_Lean_replaceRef(v_ref_3298_, v_ref_3310_);
lean_inc_ref(v_inheritedTraceOptions_3320_);
lean_inc(v_cancelTk_x3f_3318_);
lean_inc(v_currMacroScope_3316_);
lean_inc(v_quotContext_3315_);
lean_inc(v_maxHeartbeats_3314_);
lean_inc(v_initHeartbeats_3313_);
lean_inc(v_openDecls_3312_);
lean_inc(v_currNamespace_3311_);
lean_inc(v_maxRecDepth_3309_);
lean_inc(v_currRecDepth_3308_);
lean_inc_ref(v_options_3307_);
lean_inc_ref(v_fileMap_3306_);
lean_inc_ref(v_fileName_3305_);
v___x_3322_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3322_, 0, v_fileName_3305_);
lean_ctor_set(v___x_3322_, 1, v_fileMap_3306_);
lean_ctor_set(v___x_3322_, 2, v_options_3307_);
lean_ctor_set(v___x_3322_, 3, v_currRecDepth_3308_);
lean_ctor_set(v___x_3322_, 4, v_maxRecDepth_3309_);
lean_ctor_set(v___x_3322_, 5, v_ref_3321_);
lean_ctor_set(v___x_3322_, 6, v_currNamespace_3311_);
lean_ctor_set(v___x_3322_, 7, v_openDecls_3312_);
lean_ctor_set(v___x_3322_, 8, v_initHeartbeats_3313_);
lean_ctor_set(v___x_3322_, 9, v_maxHeartbeats_3314_);
lean_ctor_set(v___x_3322_, 10, v_quotContext_3315_);
lean_ctor_set(v___x_3322_, 11, v_currMacroScope_3316_);
lean_ctor_set(v___x_3322_, 12, v_cancelTk_x3f_3318_);
lean_ctor_set(v___x_3322_, 13, v_inheritedTraceOptions_3320_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*14, v_diag_3317_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*14 + 1, v_suppressElabErrors_3319_);
v___x_3323_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3299_, v___y_3300_, v___y_3301_, v___x_3322_, v___y_3303_);
lean_dec_ref(v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3324_, v_msg_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v_ref_3324_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3332_, lean_object* v_msg_3333_, lean_object* v_declHint_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v_a_3341_; lean_object* v___x_3342_; 
v___x_3340_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3333_, v_declHint_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3332_, v_a_3341_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3343_, lean_object* v_msg_3344_, lean_object* v_declHint_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3343_, v_msg_3344_, v_declHint_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v_ref_3343_);
return v_res_3351_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3355_, lean_object* v_constName_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3362_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3363_ = 0;
lean_inc(v_constName_3356_);
v___x_3364_ = l_Lean_MessageData_ofConstName(v_constName_3356_, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3362_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3355_, v___x_3367_, v_constName_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3369_, lean_object* v_constName_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3369_, v_constName_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v_ref_3369_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_ref_3383_; lean_object* v___x_3384_; 
v_ref_3383_ = lean_ctor_get(v___y_3380_, 5);
v___x_3384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3383_, v_constName_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; lean_object* v_env_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = lean_st_ref_get(v___y_3396_);
v_env_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_ref(v_env_3399_);
lean_dec(v___x_3398_);
v___x_3400_ = 0;
lean_inc(v_constName_3392_);
v___x_3401_ = l_Lean_Environment_find_x3f(v_env_3399_, v_constName_3392_, v___x_3400_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v___x_3402_;
}
else
{
lean_object* v_val_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_constName_3392_);
v_val_3403_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3401_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_val_3403_);
lean_dec(v___x_3401_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set_tag(v___x_3405_, 0);
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_val_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3417_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3425_, uint8_t v_suppressElabErrors_3426_, lean_object* v_x_3427_){
_start:
{
if (lean_obj_tag(v_x_3427_) == 1)
{
lean_object* v_pre_3428_; 
v_pre_3428_ = lean_ctor_get(v_x_3427_, 0);
switch(lean_obj_tag(v_pre_3428_))
{
case 1:
{
lean_object* v_pre_3429_; 
v_pre_3429_ = lean_ctor_get(v_pre_3428_, 0);
switch(lean_obj_tag(v_pre_3429_))
{
case 0:
{
lean_object* v_str_3430_; lean_object* v_str_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v_str_3430_ = lean_ctor_get(v_x_3427_, 1);
v_str_3431_ = lean_ctor_get(v_pre_3428_, 1);
v___x_3432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3433_ = lean_string_dec_eq(v_str_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3435_ = lean_string_dec_eq(v_str_3431_, v___x_3434_);
if (v___x_3435_ == 0)
{
return v___y_3425_;
}
else
{
lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3437_ = lean_string_dec_eq(v_str_3430_, v___x_3436_);
if (v___x_3437_ == 0)
{
return v___y_3425_;
}
else
{
return v_suppressElabErrors_3426_;
}
}
}
else
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3439_ = lean_string_dec_eq(v_str_3430_, v___x_3438_);
if (v___x_3439_ == 0)
{
return v___y_3425_;
}
else
{
return v_suppressElabErrors_3426_;
}
}
}
case 1:
{
lean_object* v_pre_3440_; 
v_pre_3440_ = lean_ctor_get(v_pre_3429_, 0);
if (lean_obj_tag(v_pre_3440_) == 0)
{
lean_object* v_str_3441_; lean_object* v_str_3442_; lean_object* v_str_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_str_3441_ = lean_ctor_get(v_x_3427_, 1);
v_str_3442_ = lean_ctor_get(v_pre_3428_, 1);
v_str_3443_ = lean_ctor_get(v_pre_3429_, 1);
v___x_3444_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3445_ = lean_string_dec_eq(v_str_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
return v___y_3425_;
}
else
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3447_ = lean_string_dec_eq(v_str_3442_, v___x_3446_);
if (v___x_3447_ == 0)
{
return v___y_3425_;
}
else
{
lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3449_ = lean_string_dec_eq(v_str_3441_, v___x_3448_);
if (v___x_3449_ == 0)
{
return v___y_3425_;
}
else
{
return v_suppressElabErrors_3426_;
}
}
}
}
else
{
return v___y_3425_;
}
}
default: 
{
return v___y_3425_;
}
}
}
case 0:
{
lean_object* v_str_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v_str_3450_ = lean_ctor_get(v_x_3427_, 1);
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3452_ = lean_string_dec_eq(v_str_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
return v___y_3425_;
}
else
{
return v_suppressElabErrors_3426_;
}
}
default: 
{
return v___y_3425_;
}
}
}
else
{
return v___y_3425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3453_, lean_object* v_suppressElabErrors_3454_, lean_object* v_x_3455_){
_start:
{
uint8_t v___y_8286__boxed_3456_; uint8_t v_suppressElabErrors_boxed_3457_; uint8_t v_res_3458_; lean_object* v_r_3459_; 
v___y_8286__boxed_3456_ = lean_unbox(v___y_3453_);
v_suppressElabErrors_boxed_3457_ = lean_unbox(v_suppressElabErrors_3454_);
v_res_3458_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8286__boxed_3456_, v_suppressElabErrors_boxed_3457_, v_x_3455_);
lean_dec(v_x_3455_);
v_r_3459_ = lean_box(v_res_3458_);
return v_r_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3460_, lean_object* v_msgData_3461_, uint8_t v_severity_3462_, uint8_t v_isSilent_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; uint8_t v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3506_; uint8_t v___y_3507_; uint8_t v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3534_; uint8_t v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; uint8_t v___x_3553_; uint8_t v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; uint8_t v___y_3561_; uint8_t v___y_3563_; uint8_t v___x_3578_; 
v___x_3553_ = 2;
v___x_3578_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3462_, v___x_3553_);
if (v___x_3578_ == 0)
{
v___y_3563_ = v___x_3578_;
goto v___jp_3562_;
}
else
{
uint8_t v___x_3579_; 
lean_inc_ref(v_msgData_3461_);
v___x_3579_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3461_);
v___y_3563_ = v___x_3579_;
goto v___jp_3562_;
}
v___jp_3469_:
{
lean_object* v___x_3479_; lean_object* v_currNamespace_3480_; lean_object* v_openDecls_3481_; lean_object* v_env_3482_; lean_object* v_nextMacroScope_3483_; lean_object* v_ngen_3484_; lean_object* v_auxDeclNGen_3485_; lean_object* v_traceState_3486_; lean_object* v_cache_3487_; lean_object* v_messages_3488_; lean_object* v_infoState_3489_; lean_object* v_snapshotTasks_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3504_; 
v___x_3479_ = lean_st_ref_take(v___y_3478_);
v_currNamespace_3480_ = lean_ctor_get(v___y_3477_, 6);
v_openDecls_3481_ = lean_ctor_get(v___y_3477_, 7);
v_env_3482_ = lean_ctor_get(v___x_3479_, 0);
v_nextMacroScope_3483_ = lean_ctor_get(v___x_3479_, 1);
v_ngen_3484_ = lean_ctor_get(v___x_3479_, 2);
v_auxDeclNGen_3485_ = lean_ctor_get(v___x_3479_, 3);
v_traceState_3486_ = lean_ctor_get(v___x_3479_, 4);
v_cache_3487_ = lean_ctor_get(v___x_3479_, 5);
v_messages_3488_ = lean_ctor_get(v___x_3479_, 6);
v_infoState_3489_ = lean_ctor_get(v___x_3479_, 7);
v_snapshotTasks_3490_ = lean_ctor_get(v___x_3479_, 8);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3492_ = v___x_3479_;
v_isShared_3493_ = v_isSharedCheck_3504_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snapshotTasks_3490_);
lean_inc(v_infoState_3489_);
lean_inc(v_messages_3488_);
lean_inc(v_cache_3487_);
lean_inc(v_traceState_3486_);
lean_inc(v_auxDeclNGen_3485_);
lean_inc(v_ngen_3484_);
lean_inc(v_nextMacroScope_3483_);
lean_inc(v_env_3482_);
lean_dec(v___x_3479_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3504_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_inc(v_openDecls_3481_);
lean_inc(v_currNamespace_3480_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v_currNamespace_3480_);
lean_ctor_set(v___x_3494_, 1, v_openDecls_3481_);
v___x_3495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v___y_3471_);
lean_inc_ref(v___y_3472_);
lean_inc_ref(v___y_3476_);
v___x_3496_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3496_, 0, v___y_3476_);
lean_ctor_set(v___x_3496_, 1, v___y_3470_);
lean_ctor_set(v___x_3496_, 2, v___y_3474_);
lean_ctor_set(v___x_3496_, 3, v___y_3472_);
lean_ctor_set(v___x_3496_, 4, v___x_3495_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*5, v___y_3475_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*5 + 1, v___y_3473_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*5 + 2, v_isSilent_3463_);
v___x_3497_ = l_Lean_MessageLog_add(v___x_3496_, v_messages_3488_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 6, v___x_3497_);
v___x_3499_ = v___x_3492_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_env_3482_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_nextMacroScope_3483_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_ngen_3484_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_auxDeclNGen_3485_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_traceState_3486_);
lean_ctor_set(v_reuseFailAlloc_3503_, 5, v_cache_3487_);
lean_ctor_set(v_reuseFailAlloc_3503_, 6, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3503_, 7, v_infoState_3489_);
lean_ctor_set(v_reuseFailAlloc_3503_, 8, v_snapshotTasks_3490_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_st_ref_set(v___y_3478_, v___x_3499_);
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
}
v___jp_3505_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3529_; 
v___x_3514_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3461_);
v___x_3515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3514_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_inc_ref_n(v___y_3511_, 2);
v___x_3520_ = l_Lean_FileMap_toPosition(v___y_3511_, v___y_3510_);
lean_dec(v___y_3510_);
v___x_3521_ = l_Lean_FileMap_toPosition(v___y_3511_, v___y_3513_);
lean_dec(v___y_3513_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3508_ == 0)
{
lean_del_object(v___x_3518_);
lean_dec_ref(v___y_3506_);
v___y_3470_ = v___x_3520_;
v___y_3471_ = v_a_3516_;
v___y_3472_ = v___x_3523_;
v___y_3473_ = v___y_3507_;
v___y_3474_ = v___x_3522_;
v___y_3475_ = v___y_3509_;
v___y_3476_ = v___y_3512_;
v___y_3477_ = v___y_3466_;
v___y_3478_ = v___y_3467_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3524_; 
lean_inc(v_a_3516_);
v___x_3524_ = l_Lean_MessageData_hasTag(v___y_3506_, v_a_3516_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
lean_dec_ref(v___x_3522_);
lean_dec_ref(v___x_3520_);
lean_dec(v_a_3516_);
v___x_3525_ = lean_box(0);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3525_);
v___x_3527_ = v___x_3518_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
else
{
lean_del_object(v___x_3518_);
v___y_3470_ = v___x_3520_;
v___y_3471_ = v_a_3516_;
v___y_3472_ = v___x_3523_;
v___y_3473_ = v___y_3507_;
v___y_3474_ = v___x_3522_;
v___y_3475_ = v___y_3509_;
v___y_3476_ = v___y_3512_;
v___y_3477_ = v___y_3466_;
v___y_3478_ = v___y_3467_;
goto v___jp_3469_;
}
}
}
}
v___jp_3530_:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Syntax_getTailPos_x3f(v___y_3532_, v___y_3535_);
lean_dec(v___y_3532_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_inc(v___y_3538_);
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3533_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3536_;
v___y_3512_ = v___y_3537_;
v___y_3513_ = v___y_3538_;
goto v___jp_3505_;
}
else
{
lean_object* v_val_3540_; 
v_val_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_val_3540_);
lean_dec_ref(v___x_3539_);
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3533_;
v___y_3508_ = v___y_3534_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3536_;
v___y_3512_ = v___y_3537_;
v___y_3513_ = v_val_3540_;
goto v___jp_3505_;
}
}
v___jp_3541_:
{
lean_object* v_ref_3549_; lean_object* v___x_3550_; 
v_ref_3549_ = l_Lean_replaceRef(v_ref_3460_, v___y_3544_);
v___x_3550_ = l_Lean_Syntax_getPos_x3f(v_ref_3549_, v___y_3545_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___y_3531_ = v___y_3542_;
v___y_3532_ = v_ref_3549_;
v___y_3533_ = v___y_3548_;
v___y_3534_ = v___y_3543_;
v___y_3535_ = v___y_3545_;
v___y_3536_ = v___y_3546_;
v___y_3537_ = v___y_3547_;
v___y_3538_ = v___x_3551_;
goto v___jp_3530_;
}
else
{
lean_object* v_val_3552_; 
v_val_3552_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_val_3552_);
lean_dec_ref(v___x_3550_);
v___y_3531_ = v___y_3542_;
v___y_3532_ = v_ref_3549_;
v___y_3533_ = v___y_3548_;
v___y_3534_ = v___y_3543_;
v___y_3535_ = v___y_3545_;
v___y_3536_ = v___y_3546_;
v___y_3537_ = v___y_3547_;
v___y_3538_ = v_val_3552_;
goto v___jp_3530_;
}
}
v___jp_3554_:
{
if (v___y_3561_ == 0)
{
v___y_3542_ = v___y_3557_;
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3560_;
v___y_3546_ = v___y_3558_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v_severity_3462_;
goto v___jp_3541_;
}
else
{
v___y_3542_ = v___y_3557_;
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3560_;
v___y_3546_ = v___y_3558_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v___x_3553_;
goto v___jp_3541_;
}
}
v___jp_3562_:
{
if (v___y_3563_ == 0)
{
lean_object* v_fileName_3564_; lean_object* v_fileMap_3565_; lean_object* v_options_3566_; lean_object* v_ref_3567_; uint8_t v_suppressElabErrors_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___f_3571_; uint8_t v___x_3572_; uint8_t v___x_3573_; 
v_fileName_3564_ = lean_ctor_get(v___y_3466_, 0);
v_fileMap_3565_ = lean_ctor_get(v___y_3466_, 1);
v_options_3566_ = lean_ctor_get(v___y_3466_, 2);
v_ref_3567_ = lean_ctor_get(v___y_3466_, 5);
v_suppressElabErrors_3568_ = lean_ctor_get_uint8(v___y_3466_, sizeof(void*)*14 + 1);
v___x_3569_ = lean_box(v___y_3563_);
v___x_3570_ = lean_box(v_suppressElabErrors_3568_);
v___f_3571_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3571_, 0, v___x_3569_);
lean_closure_set(v___f_3571_, 1, v___x_3570_);
v___x_3572_ = 1;
v___x_3573_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3462_, v___x_3572_);
if (v___x_3573_ == 0)
{
v___y_3555_ = v_suppressElabErrors_3568_;
v___y_3556_ = v_ref_3567_;
v___y_3557_ = v___f_3571_;
v___y_3558_ = v_fileMap_3565_;
v___y_3559_ = v_fileName_3564_;
v___y_3560_ = v___y_3563_;
v___y_3561_ = v___x_3573_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3574_ = l_Lean_warningAsError;
v___x_3575_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3566_, v___x_3574_);
v___y_3555_ = v_suppressElabErrors_3568_;
v___y_3556_ = v_ref_3567_;
v___y_3557_ = v___f_3571_;
v___y_3558_ = v_fileMap_3565_;
v___y_3559_ = v_fileName_3564_;
v___y_3560_ = v___y_3563_;
v___y_3561_ = v___x_3575_;
goto v___jp_3554_;
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec_ref(v_msgData_3461_);
v___x_3576_ = lean_box(0);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3580_, lean_object* v_msgData_3581_, lean_object* v_severity_3582_, lean_object* v_isSilent_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v_severity_boxed_3589_; uint8_t v_isSilent_boxed_3590_; lean_object* v_res_3591_; 
v_severity_boxed_3589_ = lean_unbox(v_severity_3582_);
v_isSilent_boxed_3590_ = lean_unbox(v_isSilent_3583_);
v_res_3591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3580_, v_msgData_3581_, v_severity_boxed_3589_, v_isSilent_boxed_3590_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v_ref_3580_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3592_, uint8_t v_severity_3593_, uint8_t v_isSilent_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_ref_3600_; lean_object* v___x_3601_; 
v_ref_3600_ = lean_ctor_get(v___y_3597_, 5);
v___x_3601_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3600_, v_msgData_3592_, v_severity_3593_, v_isSilent_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3602_, lean_object* v_severity_3603_, lean_object* v_isSilent_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
uint8_t v_severity_boxed_3610_; uint8_t v_isSilent_boxed_3611_; lean_object* v_res_3612_; 
v_severity_boxed_3610_ = lean_unbox(v_severity_3603_);
v_isSilent_boxed_3611_ = lean_unbox(v_isSilent_3604_);
v_res_3612_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3602_, v_severity_boxed_3610_, v_isSilent_boxed_3611_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
uint8_t v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = 1;
v___x_3620_ = 0;
v___x_3621_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3613_, v___x_3619_, v___x_3620_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v_env_3636_; uint8_t v___x_3637_; lean_object* v___x_3638_; 
v___x_3635_ = lean_st_ref_get(v___y_3633_);
v_env_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc_ref(v_env_3636_);
lean_dec(v___x_3635_);
v___x_3637_ = 0;
lean_inc(v_constName_3629_);
v___x_3638_ = l_Lean_Environment_findConstVal_x3f(v_env_3636_, v_constName_3629_, v___x_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3639_;
}
else
{
lean_object* v_val_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v_constName_3629_);
v_val_3640_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3638_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_val_3640_);
lean_dec(v___x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 0);
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_val_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
if (lean_obj_tag(v_a_3655_) == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = l_List_reverse___redArg(v_a_3656_);
return v___x_3657_;
}
else
{
lean_object* v_head_3658_; lean_object* v_tail_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3668_; 
v_head_3658_ = lean_ctor_get(v_a_3655_, 0);
v_tail_3659_ = lean_ctor_get(v_a_3655_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3661_ = v_a_3655_;
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_tail_3659_);
lean_inc(v_head_3658_);
lean_dec(v_a_3655_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3663_ = l_Lean_mkLevelParam(v_head_3658_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 1, v_a_3656_);
lean_ctor_set(v___x_3661_, 0, v___x_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_a_3656_);
v___x_3665_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
v_a_3655_ = v_tail_3659_;
v_a_3656_ = v___x_3665_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; 
lean_inc(v_constName_3669_);
v___x_3675_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3687_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3687_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3687_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_levelParams_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v_levelParams_3680_ = lean_ctor_get(v_a_3676_, 1);
lean_inc(v_levelParams_3680_);
lean_dec(v_a_3676_);
v___x_3681_ = lean_box(0);
v___x_3682_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_3680_, v___x_3681_);
v___x_3683_ = l_Lean_mkConst(v_constName_3669_, v___x_3682_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3683_);
v___x_3685_ = v___x_3678_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v_constName_3669_);
v_a_3688_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3675_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3675_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
return v_res_3702_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
return v___x_3708_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_3712_, uint8_t v_attrKind_3713_, lean_object* v_prio_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v___x_3720_; 
lean_inc(v_declName_3712_);
v___x_3720_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_3712_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc_n(v_a_3721_, 2);
lean_dec_ref(v___x_3720_);
v___x_3722_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_3721_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___x_3751_; lean_object* v_a_3752_; uint8_t v___x_3753_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
lean_inc(v_declName_3712_);
v___x_3751_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3712_, v_a_3718_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref(v___x_3751_);
v___x_3753_ = lean_unbox(v_a_3752_);
lean_dec(v_a_3752_);
switch(v___x_3753_)
{
case 0:
{
v___y_3725_ = v_a_3715_;
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
goto v___jp_3724_;
}
case 3:
{
v___y_3725_ = v_a_3715_;
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
goto v___jp_3724_;
}
default: 
{
lean_object* v___x_3754_; 
lean_inc(v_declName_3712_);
v___x_3754_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_3712_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; uint8_t v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___x_3754_);
v___x_3756_ = l_Lean_ConstantInfo_isDefinition(v_a_3755_);
lean_dec(v_a_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v_env_3758_; uint8_t v___x_3759_; 
v___x_3757_ = lean_st_ref_get(v_a_3718_);
v_env_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc_ref(v_env_3758_);
lean_dec(v___x_3757_);
lean_inc(v_declName_3712_);
v___x_3759_ = l_Lean_wasOriginallyDefn(v_env_3758_, v_declName_3712_);
if (v___x_3759_ == 0)
{
v___y_3725_ = v_a_3715_;
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3760_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3712_);
v___x_3761_ = l_Lean_MessageData_ofName(v_declName_3712_);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3764_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_dec_ref(v___x_3765_);
v___y_3725_ = v_a_3715_;
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
goto v___jp_3724_;
}
else
{
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
return v___x_3765_;
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3766_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3712_);
v___x_3767_ = l_Lean_MessageData_ofName(v_declName_3712_);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3770_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_dec_ref(v___x_3771_);
v___y_3725_ = v_a_3715_;
v___y_3726_ = v_a_3716_;
v___y_3727_ = v_a_3717_;
v___y_3728_ = v_a_3718_;
goto v___jp_3724_;
}
else
{
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
v_a_3772_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3754_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3754_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
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
v___jp_3724_:
{
lean_object* v___x_3729_; lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3750_; 
lean_inc(v_declName_3712_);
v___x_3729_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3712_, v___y_3728_);
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3750_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3750_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; 
lean_inc(v_a_3721_);
v___x_3734_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_3721_, v_a_3730_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref(v___x_3734_);
v___x_3736_ = l_Lean_Meta_instanceExtension;
if (v_isShared_3733_ == 0)
{
lean_ctor_set_tag(v___x_3732_, 1);
lean_ctor_set(v___x_3732_, 0, v_declName_3712_);
v___x_3738_ = v___x_3732_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_declName_3712_);
v___x_3738_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3739_, 0, v_a_3723_);
lean_ctor_set(v___x_3739_, 1, v_a_3721_);
lean_ctor_set(v___x_3739_, 2, v_prio_3714_);
lean_ctor_set(v___x_3739_, 3, v___x_3738_);
lean_ctor_set(v___x_3739_, 4, v_a_3735_);
lean_ctor_set_uint8(v___x_3739_, sizeof(void*)*5, v_attrKind_3713_);
v___x_3740_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_3736_, v___x_3739_, v_attrKind_3713_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3740_;
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3732_);
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
v_a_3742_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3734_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3734_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_a_3721_);
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
v_a_3780_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3722_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3722_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec(v_prio_3714_);
lean_dec(v_declName_3712_);
v_a_3788_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3720_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3720_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_3796_, lean_object* v_attrKind_3797_, lean_object* v_prio_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
uint8_t v_attrKind_boxed_3804_; lean_object* v_res_3805_; 
v_attrKind_boxed_3804_ = lean_unbox(v_attrKind_3797_);
v_res_3805_ = l_Lean_Meta_addInstance(v_declName_3796_, v_attrKind_boxed_3804_, v_prio_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_3806_, lean_object* v_constName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3814_, lean_object* v_constName_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_3814_, v_constName_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_3822_, lean_object* v_ref_3823_, lean_object* v_constName_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3823_, v_constName_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_ref_3832_, lean_object* v_constName_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_3831_, v_ref_3832_, v_constName_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v_ref_3832_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_3840_, lean_object* v_ref_3841_, lean_object* v_msg_3842_, lean_object* v_declHint_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3841_, v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_ref_3851_, lean_object* v_msg_3852_, lean_object* v_declHint_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_3850_, v_ref_3851_, v_msg_3852_, v_declHint_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v_ref_3851_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_3860_, lean_object* v_declHint_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3860_, v_declHint_3861_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_3868_, lean_object* v_declHint_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_3868_, v_declHint_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_3876_, lean_object* v_ref_3877_, lean_object* v_msg_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3877_, v_msg_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3885_, lean_object* v_ref_3886_, lean_object* v_msg_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_3885_, v_ref_3886_, v_msg_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v_ref_3886_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_3894_, uint8_t v_s_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; lean_object* v_env_3900_; lean_object* v_nextMacroScope_3901_; lean_object* v_ngen_3902_; lean_object* v_auxDeclNGen_3903_; lean_object* v_traceState_3904_; lean_object* v_messages_3905_; lean_object* v_infoState_3906_; lean_object* v_snapshotTasks_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3936_; 
v___x_3899_ = lean_st_ref_take(v___y_3897_);
v_env_3900_ = lean_ctor_get(v___x_3899_, 0);
v_nextMacroScope_3901_ = lean_ctor_get(v___x_3899_, 1);
v_ngen_3902_ = lean_ctor_get(v___x_3899_, 2);
v_auxDeclNGen_3903_ = lean_ctor_get(v___x_3899_, 3);
v_traceState_3904_ = lean_ctor_get(v___x_3899_, 4);
v_messages_3905_ = lean_ctor_get(v___x_3899_, 6);
v_infoState_3906_ = lean_ctor_get(v___x_3899_, 7);
v_snapshotTasks_3907_ = lean_ctor_get(v___x_3899_, 8);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v___x_3899_, 5);
lean_dec(v_unused_3937_);
v___x_3909_ = v___x_3899_;
v_isShared_3910_ = v_isSharedCheck_3936_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_snapshotTasks_3907_);
lean_inc(v_infoState_3906_);
lean_inc(v_messages_3905_);
lean_inc(v_traceState_3904_);
lean_inc(v_auxDeclNGen_3903_);
lean_inc(v_ngen_3902_);
lean_inc(v_nextMacroScope_3901_);
lean_inc(v_env_3900_);
lean_dec(v___x_3899_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3936_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3911_ = 0;
v___x_3912_ = lean_box(0);
v___x_3913_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_3900_, v_declName_3894_, v_s_3895_, v___x_3911_, v___x_3912_);
v___x_3914_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 5, v___x_3914_);
lean_ctor_set(v___x_3909_, 0, v___x_3913_);
v___x_3916_ = v___x_3909_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_nextMacroScope_3901_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_ngen_3902_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_auxDeclNGen_3903_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v_traceState_3904_);
lean_ctor_set(v_reuseFailAlloc_3935_, 5, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3935_, 6, v_messages_3905_);
lean_ctor_set(v_reuseFailAlloc_3935_, 7, v_infoState_3906_);
lean_ctor_set(v_reuseFailAlloc_3935_, 8, v_snapshotTasks_3907_);
v___x_3916_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v_mctx_3919_; lean_object* v_zetaDeltaFVarIds_3920_; lean_object* v_postponed_3921_; lean_object* v_diag_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3933_; 
v___x_3917_ = lean_st_ref_set(v___y_3897_, v___x_3916_);
v___x_3918_ = lean_st_ref_take(v___y_3896_);
v_mctx_3919_ = lean_ctor_get(v___x_3918_, 0);
v_zetaDeltaFVarIds_3920_ = lean_ctor_get(v___x_3918_, 2);
v_postponed_3921_ = lean_ctor_get(v___x_3918_, 3);
v_diag_3922_ = lean_ctor_get(v___x_3918_, 4);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v___x_3918_, 1);
lean_dec(v_unused_3934_);
v___x_3924_ = v___x_3918_;
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_diag_3922_);
lean_inc(v_postponed_3921_);
lean_inc(v_zetaDeltaFVarIds_3920_);
lean_inc(v_mctx_3919_);
lean_dec(v___x_3918_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 1, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_mctx_3919_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_zetaDeltaFVarIds_3920_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_postponed_3921_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_diag_3922_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_st_ref_set(v___y_3896_, v___x_3928_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_3938_, lean_object* v_s_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
uint8_t v_s_boxed_3943_; lean_object* v_res_3944_; 
v_s_boxed_3943_ = lean_unbox(v_s_3939_);
v_res_3944_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3938_, v_s_boxed_3943_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec(v___y_3940_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_3945_, uint8_t v_s_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3945_, v_s_3946_, v___y_3948_, v___y_3950_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_3953_, lean_object* v_s_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
uint8_t v_s_boxed_3960_; lean_object* v_res_3961_; 
v_s_boxed_3960_ = lean_unbox(v_s_3954_);
v_res_3961_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_3953_, v_s_boxed_3960_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_3962_, uint8_t v_attrKind_3963_, lean_object* v_prio_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = 3;
lean_inc(v_declName_3962_);
v___x_3971_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3962_, v___x_3970_, v_a_3966_, v_a_3968_);
lean_dec_ref(v___x_3971_);
v___x_3972_ = l_Lean_Meta_addInstance(v_declName_3962_, v_attrKind_3963_, v_prio_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_3973_, lean_object* v_attrKind_3974_, lean_object* v_prio_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
uint8_t v_attrKind_boxed_3981_; lean_object* v_res_3982_; 
v_attrKind_boxed_3981_ = lean_unbox(v_attrKind_3974_);
v_res_3982_ = l_Lean_Meta_registerInstance(v_declName_3973_, v_attrKind_boxed_3981_, v_prio_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_3983_, lean_object* v_x_3984_){
_start:
{
lean_inc_ref(v_a_3983_);
return v_a_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_3985_, lean_object* v_x_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_3985_, v_x_3986_);
lean_dec_ref(v_x_3986_);
lean_dec_ref(v_a_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v_env_3993_; lean_object* v_options_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3992_ = lean_st_ref_get(v___y_3990_);
v_env_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc_ref(v_env_3993_);
lean_dec(v___x_3992_);
v_options_3994_ = lean_ctor_get(v___y_3989_, 2);
v___x_3995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3996_ = lean_unsigned_to_nat(32u);
v___x_3997_ = lean_mk_empty_array_with_capacity(v___x_3996_);
lean_dec_ref(v___x_3997_);
v___x_3998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3994_);
v___x_3999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3999_, 0, v_env_3993_);
lean_ctor_set(v___x_3999_, 1, v___x_3995_);
lean_ctor_set(v___x_3999_, 2, v___x_3998_);
lean_ctor_set(v___x_3999_, 3, v_options_3994_);
v___x_4000_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v_msgData_3988_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_ref_4011_; lean_object* v___x_4012_; lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4021_; 
v_ref_4011_ = lean_ctor_get(v___y_4008_, 5);
v___x_4012_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4007_, v___y_4008_, v___y_4009_);
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4021_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4021_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
lean_inc(v_ref_4011_);
v___x_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4017_, 0, v_ref_4011_);
lean_ctor_set(v___x_4017_, 1, v_a_4013_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 1);
lean_ctor_set(v___x_4015_, 0, v___x_4017_);
v___x_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4027_, lean_object* v_i_4028_, lean_object* v_k_4029_){
_start:
{
lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4030_ = lean_array_get_size(v_keys_4027_);
v___x_4031_ = lean_nat_dec_lt(v_i_4028_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_dec(v_i_4028_);
return v___x_4031_;
}
else
{
lean_object* v_k_x27_4032_; uint8_t v___x_4033_; 
v_k_x27_4032_ = lean_array_fget_borrowed(v_keys_4027_, v_i_4028_);
v___x_4033_ = lean_name_eq(v_k_4029_, v_k_x27_4032_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_unsigned_to_nat(1u);
v___x_4035_ = lean_nat_add(v_i_4028_, v___x_4034_);
lean_dec(v_i_4028_);
v_i_4028_ = v___x_4035_;
goto _start;
}
else
{
lean_dec(v_i_4028_);
return v___x_4033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4037_, lean_object* v_i_4038_, lean_object* v_k_4039_){
_start:
{
uint8_t v_res_4040_; lean_object* v_r_4041_; 
v_res_4040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4037_, v_i_4038_, v_k_4039_);
lean_dec(v_k_4039_);
lean_dec_ref(v_keys_4037_);
v_r_4041_ = lean_box(v_res_4040_);
return v_r_4041_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4042_, size_t v_x_4043_, lean_object* v_x_4044_){
_start:
{
if (lean_obj_tag(v_x_4042_) == 0)
{
lean_object* v_es_4045_; lean_object* v___x_4046_; size_t v___x_4047_; size_t v___x_4048_; size_t v___x_4049_; lean_object* v_j_4050_; lean_object* v___x_4051_; 
v_es_4045_ = lean_ctor_get(v_x_4042_, 0);
v___x_4046_ = lean_box(2);
v___x_4047_ = ((size_t)5ULL);
v___x_4048_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4049_ = lean_usize_land(v_x_4043_, v___x_4048_);
v_j_4050_ = lean_usize_to_nat(v___x_4049_);
v___x_4051_ = lean_array_get_borrowed(v___x_4046_, v_es_4045_, v_j_4050_);
lean_dec(v_j_4050_);
switch(lean_obj_tag(v___x_4051_))
{
case 0:
{
lean_object* v_key_4052_; uint8_t v___x_4053_; 
v_key_4052_ = lean_ctor_get(v___x_4051_, 0);
v___x_4053_ = lean_name_eq(v_x_4044_, v_key_4052_);
return v___x_4053_;
}
case 1:
{
lean_object* v_node_4054_; size_t v___x_4055_; 
v_node_4054_ = lean_ctor_get(v___x_4051_, 0);
v___x_4055_ = lean_usize_shift_right(v_x_4043_, v___x_4047_);
v_x_4042_ = v_node_4054_;
v_x_4043_ = v___x_4055_;
goto _start;
}
default: 
{
uint8_t v___x_4057_; 
v___x_4057_ = 0;
return v___x_4057_;
}
}
}
else
{
lean_object* v_ks_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_ks_4058_ = lean_ctor_get(v_x_4042_, 0);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4058_, v___x_4059_, v_x_4044_);
return v___x_4060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4061_, lean_object* v_x_4062_, lean_object* v_x_4063_){
_start:
{
size_t v_x_2352__boxed_4064_; uint8_t v_res_4065_; lean_object* v_r_4066_; 
v_x_2352__boxed_4064_ = lean_unbox_usize(v_x_4062_);
lean_dec(v_x_4062_);
v_res_4065_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4061_, v_x_2352__boxed_4064_, v_x_4063_);
lean_dec(v_x_4063_);
lean_dec_ref(v_x_4061_);
v_r_4066_ = lean_box(v_res_4065_);
return v_r_4066_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4067_, lean_object* v_x_4068_){
_start:
{
uint64_t v___y_4070_; 
if (lean_obj_tag(v_x_4068_) == 0)
{
uint64_t v___x_4073_; 
v___x_4073_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4070_ = v___x_4073_;
goto v___jp_4069_;
}
else
{
uint64_t v_hash_4074_; 
v_hash_4074_ = lean_ctor_get_uint64(v_x_4068_, sizeof(void*)*2);
v___y_4070_ = v_hash_4074_;
goto v___jp_4069_;
}
v___jp_4069_:
{
size_t v___x_4071_; uint8_t v___x_4072_; 
v___x_4071_ = lean_uint64_to_usize(v___y_4070_);
v___x_4072_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4067_, v___x_4071_, v_x_4068_);
return v___x_4072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4075_, lean_object* v_x_4076_){
_start:
{
uint8_t v_res_4077_; lean_object* v_r_4078_; 
v_res_4077_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4075_, v_x_4076_);
lean_dec(v_x_4076_);
lean_dec_ref(v_x_4075_);
v_r_4078_ = lean_box(v_res_4077_);
return v_r_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4079_, lean_object* v_declName_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_instanceNames_4087_; uint8_t v___x_4088_; 
v_instanceNames_4087_ = lean_ctor_get(v_d_4079_, 1);
v___x_4088_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4087_, v_declName_4080_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec_ref(v_d_4079_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4090_ = l_Lean_MessageData_ofConstName(v_declName_4080_, v___x_4088_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4093_, v___y_4081_, v___y_4082_);
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4094_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
else
{
goto v___jp_4084_;
}
v___jp_4084_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = l_Lean_Meta_Instances_eraseCore(v_d_4079_, v_declName_4080_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4103_, lean_object* v_declName_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4103_, v_declName_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4109_, lean_object* v_declName_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; lean_object* v_env_4115_; lean_object* v___x_4116_; lean_object* v_ext_4117_; lean_object* v_toEnvExtension_4118_; lean_object* v_asyncMode_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4114_ = lean_st_ref_get(v___y_4112_);
v_env_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc_ref(v_env_4115_);
lean_dec(v___x_4114_);
v___x_4116_ = l_Lean_Meta_instanceExtension;
v_ext_4117_ = lean_ctor_get(v___x_4116_, 1);
v_toEnvExtension_4118_ = lean_ctor_get(v_ext_4117_, 0);
v_asyncMode_4119_ = lean_ctor_get(v_toEnvExtension_4118_, 2);
v___x_4120_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4109_, v___x_4116_, v_env_4115_, v_asyncMode_4119_);
v___x_4121_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4120_, v_declName_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4151_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4124_ = v___x_4121_;
v_isShared_4125_ = v_isSharedCheck_4151_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4121_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4151_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v_env_4127_; lean_object* v_nextMacroScope_4128_; lean_object* v_ngen_4129_; lean_object* v_auxDeclNGen_4130_; lean_object* v_traceState_4131_; lean_object* v_messages_4132_; lean_object* v_infoState_4133_; lean_object* v_snapshotTasks_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4149_; 
v___x_4126_ = lean_st_ref_take(v___y_4112_);
v_env_4127_ = lean_ctor_get(v___x_4126_, 0);
v_nextMacroScope_4128_ = lean_ctor_get(v___x_4126_, 1);
v_ngen_4129_ = lean_ctor_get(v___x_4126_, 2);
v_auxDeclNGen_4130_ = lean_ctor_get(v___x_4126_, 3);
v_traceState_4131_ = lean_ctor_get(v___x_4126_, 4);
v_messages_4132_ = lean_ctor_get(v___x_4126_, 6);
v_infoState_4133_ = lean_ctor_get(v___x_4126_, 7);
v_snapshotTasks_4134_ = lean_ctor_get(v___x_4126_, 8);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4149_ == 0)
{
lean_object* v_unused_4150_; 
v_unused_4150_ = lean_ctor_get(v___x_4126_, 5);
lean_dec(v_unused_4150_);
v___x_4136_ = v___x_4126_;
v_isShared_4137_ = v_isSharedCheck_4149_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_snapshotTasks_4134_);
lean_inc(v_infoState_4133_);
lean_inc(v_messages_4132_);
lean_inc(v_traceState_4131_);
lean_inc(v_auxDeclNGen_4130_);
lean_inc(v_ngen_4129_);
lean_inc(v_nextMacroScope_4128_);
lean_inc(v_env_4127_);
lean_dec(v___x_4126_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4149_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___f_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___f_4138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4138_, 0, v_a_4122_);
v___x_4139_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4116_, v_env_4127_, v___f_4138_);
v___x_4140_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 5, v___x_4140_);
lean_ctor_set(v___x_4136_, 0, v___x_4139_);
v___x_4142_ = v___x_4136_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v_nextMacroScope_4128_);
lean_ctor_set(v_reuseFailAlloc_4148_, 2, v_ngen_4129_);
lean_ctor_set(v_reuseFailAlloc_4148_, 3, v_auxDeclNGen_4130_);
lean_ctor_set(v_reuseFailAlloc_4148_, 4, v_traceState_4131_);
lean_ctor_set(v_reuseFailAlloc_4148_, 5, v___x_4140_);
lean_ctor_set(v_reuseFailAlloc_4148_, 6, v_messages_4132_);
lean_ctor_set(v_reuseFailAlloc_4148_, 7, v_infoState_4133_);
lean_ctor_set(v_reuseFailAlloc_4148_, 8, v_snapshotTasks_4134_);
v___x_4142_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4143_ = lean_st_ref_set(v___y_4112_, v___x_4142_);
v___x_4144_ = lean_box(0);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4144_);
v___x_4146_ = v___x_4124_;
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
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_a_4152_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4121_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4121_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4160_, lean_object* v_declName_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4160_, v_declName_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec_ref(v___x_4160_);
return v_res_4165_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4172_; uint64_t v___x_4173_; 
v___x_4172_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4173_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4172_);
return v___x_4173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4174_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4175_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
lean_ctor_set_uint64(v___x_4176_, sizeof(void*)*1, v___x_4174_);
return v___x_4176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4181_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
lean_ctor_set(v___x_4181_, 2, v___x_4180_);
lean_ctor_set(v___x_4181_, 3, v___x_4180_);
lean_ctor_set(v___x_4181_, 4, v___x_4180_);
lean_ctor_set(v___x_4181_, 5, v___x_4180_);
return v___x_4181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
lean_ctor_set(v___x_4183_, 3, v___x_4182_);
lean_ctor_set(v___x_4183_, 4, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v_declName_4186_, lean_object* v_stx_4187_, uint8_t v_attrKind_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4192_);
v___x_4194_ = l_Lean_getAttrParamOptPrio(v___x_4193_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; uint8_t v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; size_t v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref(v___x_4194_);
v___x_4196_ = 0;
v___x_4197_ = 1;
v___x_4198_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4199_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4200_ = lean_unsigned_to_nat(32u);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4200_);
v___x_4202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4203_ = ((size_t)5ULL);
lean_inc_n(v___x_4184_, 5);
v___x_4204_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4201_);
lean_ctor_set(v___x_4204_, 2, v___x_4184_);
lean_ctor_set(v___x_4204_, 3, v___x_4184_);
lean_ctor_set_usize(v___x_4204_, 4, v___x_4203_);
v___x_4205_ = lean_box(1);
lean_inc_ref(v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4199_);
lean_ctor_set(v___x_4206_, 1, v___x_4204_);
lean_ctor_set(v___x_4206_, 2, v___x_4205_);
v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4184_);
v___x_4208_ = lean_box(0);
lean_inc(v___x_4185_);
v___x_4209_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4209_, 0, v___x_4198_);
lean_ctor_set(v___x_4209_, 1, v___x_4185_);
lean_ctor_set(v___x_4209_, 2, v___x_4206_);
lean_ctor_set(v___x_4209_, 3, v___x_4207_);
lean_ctor_set(v___x_4209_, 4, v___x_4208_);
lean_ctor_set(v___x_4209_, 5, v___x_4184_);
lean_ctor_set(v___x_4209_, 6, v___x_4208_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7, v___x_4196_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 1, v___x_4196_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 2, v___x_4196_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 3, v___x_4197_);
v___x_4210_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4184_);
lean_ctor_set(v___x_4210_, 1, v___x_4184_);
lean_ctor_set(v___x_4210_, 2, v___x_4184_);
lean_ctor_set(v___x_4210_, 3, v___x_4199_);
lean_ctor_set(v___x_4210_, 4, v___x_4199_);
lean_ctor_set(v___x_4210_, 5, v___x_4199_);
lean_ctor_set(v___x_4210_, 6, v___x_4199_);
lean_ctor_set(v___x_4210_, 7, v___x_4199_);
lean_ctor_set(v___x_4210_, 8, v___x_4199_);
v___x_4211_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4212_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4210_);
lean_ctor_set(v___x_4213_, 1, v___x_4211_);
lean_ctor_set(v___x_4213_, 2, v___x_4185_);
lean_ctor_set(v___x_4213_, 3, v___x_4204_);
lean_ctor_set(v___x_4213_, 4, v___x_4212_);
v___x_4214_ = lean_st_mk_ref(v___x_4213_);
v___x_4215_ = l_Lean_Meta_addInstance(v_declName_4186_, v_attrKind_4188_, v_a_4195_, v___x_4209_, v___x_4214_, v___y_4189_, v___y_4190_);
lean_dec_ref(v___x_4209_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4224_; 
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4224_ == 0)
{
lean_object* v_unused_4225_; 
v_unused_4225_ = lean_ctor_get(v___x_4215_, 0);
lean_dec(v_unused_4225_);
v___x_4217_ = v___x_4215_;
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
else
{
lean_dec(v___x_4215_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
v___x_4219_ = lean_st_ref_get(v___x_4214_);
lean_dec(v___x_4214_);
lean_dec(v___x_4219_);
v___x_4220_ = lean_box(0);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4220_);
v___x_4222_ = v___x_4217_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
else
{
lean_dec(v___x_4214_);
return v___x_4215_;
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec(v_declName_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
v_a_4226_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4194_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4194_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4234_, lean_object* v___x_4235_, lean_object* v_declName_4236_, lean_object* v_stx_4237_, lean_object* v_attrKind_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
uint8_t v_attrKind_boxed_4242_; lean_object* v_res_4243_; 
v_attrKind_boxed_4242_ = lean_unbox(v_attrKind_4238_);
v_res_4243_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4234_, v___x_4235_, v_declName_4236_, v_stx_4237_, v_attrKind_boxed_4242_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v_stx_4237_);
return v_res_4243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4244_; lean_object* v___f_4245_; 
v___x_4244_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4245_, 0, v___x_4244_);
return v___f_4245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___f_4312_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4313_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4314_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
lean_ctor_set(v___x_4315_, 1, v___f_4313_);
lean_ctor_set(v___x_4315_, 2, v___f_4312_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4318_ = l_Lean_registerBuiltinAttribute(v___x_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4320_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4321_, lean_object* v_x_4322_, lean_object* v_x_4323_){
_start:
{
uint8_t v___x_4324_; 
v___x_4324_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4322_, v_x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4325_, lean_object* v_x_4326_, lean_object* v_x_4327_){
_start:
{
uint8_t v_res_4328_; lean_object* v_r_4329_; 
v_res_4328_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4325_, v_x_4326_, v_x_4327_);
lean_dec(v_x_4327_);
lean_dec_ref(v_x_4326_);
v_r_4329_ = lean_box(v_res_4328_);
return v_r_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4330_, lean_object* v_msg_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4331_, v___y_4332_, v___y_4333_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4336_, lean_object* v_msg_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4336_, v_msg_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4342_, lean_object* v_x_4343_, size_t v_x_4344_, lean_object* v_x_4345_){
_start:
{
uint8_t v___x_4346_; 
v___x_4346_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4343_, v_x_4344_, v_x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4347_, lean_object* v_x_4348_, lean_object* v_x_4349_, lean_object* v_x_4350_){
_start:
{
size_t v_x_3004__boxed_4351_; uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_x_3004__boxed_4351_ = lean_unbox_usize(v_x_4349_);
lean_dec(v_x_4349_);
v_res_4352_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4347_, v_x_4348_, v_x_3004__boxed_4351_, v_x_4350_);
lean_dec(v_x_4350_);
lean_dec_ref(v_x_4348_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4354_, lean_object* v_keys_4355_, lean_object* v_vals_4356_, lean_object* v_heq_4357_, lean_object* v_i_4358_, lean_object* v_k_4359_){
_start:
{
uint8_t v___x_4360_; 
v___x_4360_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4355_, v_i_4358_, v_k_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4361_, lean_object* v_keys_4362_, lean_object* v_vals_4363_, lean_object* v_heq_4364_, lean_object* v_i_4365_, lean_object* v_k_4366_){
_start:
{
uint8_t v_res_4367_; lean_object* v_r_4368_; 
v_res_4367_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4361_, v_keys_4362_, v_vals_4363_, v_heq_4364_, v_i_4365_, v_k_4366_);
lean_dec(v_k_4366_);
lean_dec_ref(v_vals_4363_);
lean_dec_ref(v_keys_4362_);
v_r_4368_ = lean_box(v_res_4367_);
return v_r_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4373_ = l_Lean_addBuiltinDocString(v___x_4371_, v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v_env_4379_; lean_object* v___x_4380_; lean_object* v_ext_4381_; lean_object* v_toEnvExtension_4382_; lean_object* v_asyncMode_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v_discrTree_4386_; lean_object* v___x_4387_; 
v___x_4378_ = lean_st_ref_get(v_a_4376_);
v_env_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc_ref(v_env_4379_);
lean_dec(v___x_4378_);
v___x_4380_ = l_Lean_Meta_instanceExtension;
v_ext_4381_ = lean_ctor_get(v___x_4380_, 1);
v_toEnvExtension_4382_ = lean_ctor_get(v_ext_4381_, 0);
v_asyncMode_4383_ = lean_ctor_get(v_toEnvExtension_4382_, 2);
v___x_4384_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4385_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4384_, v___x_4380_, v_env_4379_, v_asyncMode_4383_);
v_discrTree_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc_ref(v_discrTree_4386_);
lean_dec(v___x_4385_);
v___x_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4387_, 0, v_discrTree_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4388_);
lean_dec(v_a_4388_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4395_, v_a_4396_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4399_){
_start:
{
lean_object* v___x_4401_; lean_object* v_env_4402_; lean_object* v___x_4403_; lean_object* v_ext_4404_; lean_object* v_toEnvExtension_4405_; lean_object* v_asyncMode_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_erased_4409_; lean_object* v___x_4410_; 
v___x_4401_ = lean_st_ref_get(v_a_4399_);
v_env_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_ref(v_env_4402_);
lean_dec(v___x_4401_);
v___x_4403_ = l_Lean_Meta_instanceExtension;
v_ext_4404_ = lean_ctor_get(v___x_4403_, 1);
v_toEnvExtension_4405_ = lean_ctor_get(v_ext_4404_, 0);
v_asyncMode_4406_ = lean_ctor_get(v_toEnvExtension_4405_, 2);
v___x_4407_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4408_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4407_, v___x_4403_, v_env_4402_, v_asyncMode_4406_);
v_erased_4409_ = lean_ctor_get(v___x_4408_, 2);
lean_inc_ref(v_erased_4409_);
lean_dec(v___x_4408_);
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_erased_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4411_);
lean_dec(v_a_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Meta_getErasedInstances(v_a_4418_, v_a_4419_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
return v_res_4421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4422_, lean_object* v_declName_4423_){
_start:
{
lean_object* v___x_4424_; lean_object* v_ext_4425_; lean_object* v_toEnvExtension_4426_; lean_object* v_asyncMode_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v_instanceNames_4430_; uint8_t v___x_4431_; 
v___x_4424_ = l_Lean_Meta_instanceExtension;
v_ext_4425_ = lean_ctor_get(v___x_4424_, 1);
v_toEnvExtension_4426_ = lean_ctor_get(v_ext_4425_, 0);
v_asyncMode_4427_ = lean_ctor_get(v_toEnvExtension_4426_, 2);
v___x_4428_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4429_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4428_, v___x_4424_, v_env_4422_, v_asyncMode_4427_);
v_instanceNames_4430_ = lean_ctor_get(v___x_4429_, 1);
lean_inc_ref(v_instanceNames_4430_);
lean_dec(v___x_4429_);
v___x_4431_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4430_, v_declName_4423_);
lean_dec_ref(v_instanceNames_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4432_, lean_object* v_declName_4433_){
_start:
{
uint8_t v_res_4434_; lean_object* v_r_4435_; 
v_res_4434_ = l_Lean_Meta_isInstanceCore(v_env_4432_, v_declName_4433_);
lean_dec(v_declName_4433_);
v_r_4435_ = lean_box(v_res_4434_);
return v_r_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v_env_4440_; uint8_t v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4439_ = lean_st_ref_get(v_a_4437_);
v_env_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc_ref(v_env_4440_);
lean_dec(v___x_4439_);
v___x_4441_ = l_Lean_Meta_isInstanceCore(v_env_4440_, v_declName_4436_);
v___x_4442_ = lean_box(v___x_4441_);
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_Meta_isInstance___redArg(v_declName_4444_, v_a_4445_);
lean_dec(v_a_4445_);
lean_dec(v_declName_4444_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Lean_Meta_isInstance___redArg(v_declName_4448_, v_a_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_Meta_isInstance(v_declName_4453_, v_a_4454_, v_a_4455_);
lean_dec(v_a_4455_);
lean_dec_ref(v_a_4454_);
lean_dec(v_declName_4453_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4458_, lean_object* v_vals_4459_, lean_object* v_i_4460_, lean_object* v_k_4461_){
_start:
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = lean_array_get_size(v_keys_4458_);
v___x_4463_ = lean_nat_dec_lt(v_i_4460_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; 
lean_dec(v_i_4460_);
v___x_4464_ = lean_box(0);
return v___x_4464_;
}
else
{
lean_object* v_k_x27_4465_; uint8_t v___x_4466_; 
v_k_x27_4465_ = lean_array_fget_borrowed(v_keys_4458_, v_i_4460_);
v___x_4466_ = lean_name_eq(v_k_4461_, v_k_x27_4465_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_add(v_i_4460_, v___x_4467_);
lean_dec(v_i_4460_);
v_i_4460_ = v___x_4468_;
goto _start;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_array_fget_borrowed(v_vals_4459_, v_i_4460_);
lean_dec(v_i_4460_);
lean_inc(v___x_4470_);
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4472_, lean_object* v_vals_4473_, lean_object* v_i_4474_, lean_object* v_k_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4472_, v_vals_4473_, v_i_4474_, v_k_4475_);
lean_dec(v_k_4475_);
lean_dec_ref(v_vals_4473_);
lean_dec_ref(v_keys_4472_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4477_, size_t v_x_4478_, lean_object* v_x_4479_){
_start:
{
if (lean_obj_tag(v_x_4477_) == 0)
{
lean_object* v_es_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4501_; 
v_es_4480_ = lean_ctor_get(v_x_4477_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4477_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4482_ = v_x_4477_;
v_isShared_4483_ = v_isSharedCheck_4501_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_es_4480_);
lean_dec(v_x_4477_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4501_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; size_t v___x_4485_; size_t v___x_4486_; size_t v___x_4487_; lean_object* v_j_4488_; lean_object* v___x_4489_; 
v___x_4484_ = lean_box(2);
v___x_4485_ = ((size_t)5ULL);
v___x_4486_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4487_ = lean_usize_land(v_x_4478_, v___x_4486_);
v_j_4488_ = lean_usize_to_nat(v___x_4487_);
v___x_4489_ = lean_array_get(v___x_4484_, v_es_4480_, v_j_4488_);
lean_dec(v_j_4488_);
lean_dec_ref(v_es_4480_);
switch(lean_obj_tag(v___x_4489_))
{
case 0:
{
lean_object* v_key_4490_; lean_object* v_val_4491_; uint8_t v___x_4492_; 
v_key_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_key_4490_);
v_val_4491_ = lean_ctor_get(v___x_4489_, 1);
lean_inc(v_val_4491_);
lean_dec_ref(v___x_4489_);
v___x_4492_ = lean_name_eq(v_x_4479_, v_key_4490_);
lean_dec(v_key_4490_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_dec(v_val_4491_);
lean_del_object(v___x_4482_);
v___x_4493_ = lean_box(0);
return v___x_4493_;
}
else
{
lean_object* v___x_4495_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set_tag(v___x_4482_, 1);
lean_ctor_set(v___x_4482_, 0, v_val_4491_);
v___x_4495_ = v___x_4482_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_val_4491_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
case 1:
{
lean_object* v_node_4497_; size_t v___x_4498_; 
lean_del_object(v___x_4482_);
v_node_4497_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_node_4497_);
lean_dec_ref(v___x_4489_);
v___x_4498_ = lean_usize_shift_right(v_x_4478_, v___x_4485_);
v_x_4477_ = v_node_4497_;
v_x_4478_ = v___x_4498_;
goto _start;
}
default: 
{
lean_object* v___x_4500_; 
lean_del_object(v___x_4482_);
v___x_4500_ = lean_box(0);
return v___x_4500_;
}
}
}
}
else
{
lean_object* v_ks_4502_; lean_object* v_vs_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v_ks_4502_ = lean_ctor_get(v_x_4477_, 0);
lean_inc_ref(v_ks_4502_);
v_vs_4503_ = lean_ctor_get(v_x_4477_, 1);
lean_inc_ref(v_vs_4503_);
lean_dec_ref(v_x_4477_);
v___x_4504_ = lean_unsigned_to_nat(0u);
v___x_4505_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4502_, v_vs_4503_, v___x_4504_, v_x_4479_);
lean_dec_ref(v_vs_4503_);
lean_dec_ref(v_ks_4502_);
return v___x_4505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4506_, lean_object* v_x_4507_, lean_object* v_x_4508_){
_start:
{
size_t v_x_489__boxed_4509_; lean_object* v_res_4510_; 
v_x_489__boxed_4509_ = lean_unbox_usize(v_x_4507_);
lean_dec(v_x_4507_);
v_res_4510_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4506_, v_x_489__boxed_4509_, v_x_4508_);
lean_dec(v_x_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4511_, lean_object* v_x_4512_){
_start:
{
uint64_t v___y_4514_; 
if (lean_obj_tag(v_x_4512_) == 0)
{
uint64_t v___x_4517_; 
v___x_4517_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4514_ = v___x_4517_;
goto v___jp_4513_;
}
else
{
uint64_t v_hash_4518_; 
v_hash_4518_ = lean_ctor_get_uint64(v_x_4512_, sizeof(void*)*2);
v___y_4514_ = v_hash_4518_;
goto v___jp_4513_;
}
v___jp_4513_:
{
size_t v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_uint64_to_usize(v___y_4514_);
v___x_4516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4511_, v___x_4515_, v_x_4512_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4519_, lean_object* v_x_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4519_, v_x_4520_);
lean_dec(v_x_4520_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v_env_4526_; lean_object* v___x_4527_; lean_object* v_ext_4528_; lean_object* v_toEnvExtension_4529_; lean_object* v_asyncMode_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v_instanceNames_4533_; lean_object* v___x_4534_; 
v___x_4525_ = lean_st_ref_get(v_a_4523_);
v_env_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc_ref(v_env_4526_);
lean_dec(v___x_4525_);
v___x_4527_ = l_Lean_Meta_instanceExtension;
v_ext_4528_ = lean_ctor_get(v___x_4527_, 1);
v_toEnvExtension_4529_ = lean_ctor_get(v_ext_4528_, 0);
v_asyncMode_4530_ = lean_ctor_get(v_toEnvExtension_4529_, 2);
v___x_4531_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4532_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4531_, v___x_4527_, v_env_4526_, v_asyncMode_4530_);
v_instanceNames_4533_ = lean_ctor_get(v___x_4532_, 1);
lean_inc_ref(v_instanceNames_4533_);
lean_dec(v___x_4532_);
v___x_4534_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4533_, v_declName_4522_);
if (lean_obj_tag(v___x_4534_) == 1)
{
lean_object* v_val_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4544_; 
v_val_4535_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4537_ = v___x_4534_;
v_isShared_4538_ = v_isSharedCheck_4544_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_val_4535_);
lean_dec(v___x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4544_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v_priority_4539_; lean_object* v___x_4541_; 
v_priority_4539_ = lean_ctor_get(v_val_4535_, 2);
lean_inc(v_priority_4539_);
lean_dec(v_val_4535_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v_priority_4539_);
v___x_4541_ = v___x_4537_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_priority_4539_);
v___x_4541_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
lean_dec(v___x_4534_);
v___x_4545_ = lean_box(0);
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec(v_declName_4547_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4551_, v_a_4553_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4556_, v_a_4557_, v_a_4558_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
lean_dec(v_declName_4556_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4561_, lean_object* v_x_4562_, lean_object* v_x_4563_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4562_, v_x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4565_, lean_object* v_x_4566_, lean_object* v_x_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4565_, v_x_4566_, v_x_4567_);
lean_dec(v_x_4567_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4569_, lean_object* v_x_4570_, size_t v_x_4571_, lean_object* v_x_4572_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4570_, v_x_4571_, v_x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4574_, lean_object* v_x_4575_, lean_object* v_x_4576_, lean_object* v_x_4577_){
_start:
{
size_t v_x_617__boxed_4578_; lean_object* v_res_4579_; 
v_x_617__boxed_4578_ = lean_unbox_usize(v_x_4576_);
lean_dec(v_x_4576_);
v_res_4579_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4574_, v_x_4575_, v_x_617__boxed_4578_, v_x_4577_);
lean_dec(v_x_4577_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4580_, lean_object* v_keys_4581_, lean_object* v_vals_4582_, lean_object* v_heq_4583_, lean_object* v_i_4584_, lean_object* v_k_4585_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4581_, v_vals_4582_, v_i_4584_, v_k_4585_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4587_, lean_object* v_keys_4588_, lean_object* v_vals_4589_, lean_object* v_heq_4590_, lean_object* v_i_4591_, lean_object* v_k_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4587_, v_keys_4588_, v_vals_4589_, v_heq_4590_, v_i_4591_, v_k_4592_);
lean_dec(v_k_4592_);
lean_dec_ref(v_vals_4589_);
lean_dec_ref(v_keys_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v___x_4597_; lean_object* v_env_4598_; lean_object* v___x_4599_; lean_object* v_ext_4600_; lean_object* v_toEnvExtension_4601_; lean_object* v_asyncMode_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v_instanceNames_4605_; lean_object* v___x_4606_; 
v___x_4597_ = lean_st_ref_get(v_a_4595_);
v_env_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc_ref(v_env_4598_);
lean_dec(v___x_4597_);
v___x_4599_ = l_Lean_Meta_instanceExtension;
v_ext_4600_ = lean_ctor_get(v___x_4599_, 1);
v_toEnvExtension_4601_ = lean_ctor_get(v_ext_4600_, 0);
v_asyncMode_4602_ = lean_ctor_get(v_toEnvExtension_4601_, 2);
v___x_4603_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4604_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4603_, v___x_4599_, v_env_4598_, v_asyncMode_4602_);
v_instanceNames_4605_ = lean_ctor_get(v___x_4604_, 1);
lean_inc_ref(v_instanceNames_4605_);
lean_dec(v___x_4604_);
v___x_4606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4605_, v_declName_4594_);
if (lean_obj_tag(v___x_4606_) == 1)
{
lean_object* v_val_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4617_; 
v_val_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4617_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_val_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4617_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
uint8_t v_attrKind_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v_attrKind_4611_ = lean_ctor_get_uint8(v_val_4607_, sizeof(void*)*5);
lean_dec(v_val_4607_);
v___x_4612_ = lean_box(v_attrKind_4611_);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4612_);
v___x_4614_ = v___x_4609_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
lean_dec(v___x_4606_);
v___x_4618_ = lean_box(0);
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4620_, v_a_4621_);
lean_dec(v_a_4621_);
lean_dec(v_declName_4620_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4624_, v_a_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4629_, v_a_4630_, v_a_4631_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_declName_4629_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_4638_, lean_object* v_v_4639_, lean_object* v_t_4640_){
_start:
{
if (lean_obj_tag(v_t_4640_) == 0)
{
lean_object* v_size_4641_; lean_object* v_k_4642_; lean_object* v_v_4643_; lean_object* v_l_4644_; lean_object* v_r_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4926_; 
v_size_4641_ = lean_ctor_get(v_t_4640_, 0);
v_k_4642_ = lean_ctor_get(v_t_4640_, 1);
v_v_4643_ = lean_ctor_get(v_t_4640_, 2);
v_l_4644_ = lean_ctor_get(v_t_4640_, 3);
v_r_4645_ = lean_ctor_get(v_t_4640_, 4);
v_isSharedCheck_4926_ = !lean_is_exclusive(v_t_4640_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4647_ = v_t_4640_;
v_isShared_4648_ = v_isSharedCheck_4926_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_r_4645_);
lean_inc(v_l_4644_);
lean_inc(v_v_4643_);
lean_inc(v_k_4642_);
lean_inc(v_size_4641_);
lean_dec(v_t_4640_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4926_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
uint8_t v___x_4649_; 
v___x_4649_ = lean_nat_dec_lt(v_k_4642_, v_k_4638_);
if (v___x_4649_ == 0)
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_nat_dec_eq(v_k_4642_, v_k_4638_);
if (v___x_4650_ == 0)
{
lean_object* v_impl_4651_; lean_object* v___x_4652_; 
lean_dec(v_size_4641_);
v_impl_4651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4638_, v_v_4639_, v_r_4645_);
v___x_4652_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4644_) == 0)
{
lean_object* v_size_4653_; lean_object* v_size_4654_; lean_object* v_k_4655_; lean_object* v_v_4656_; lean_object* v_l_4657_; lean_object* v_r_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v_size_4653_ = lean_ctor_get(v_l_4644_, 0);
v_size_4654_ = lean_ctor_get(v_impl_4651_, 0);
lean_inc(v_size_4654_);
v_k_4655_ = lean_ctor_get(v_impl_4651_, 1);
lean_inc(v_k_4655_);
v_v_4656_ = lean_ctor_get(v_impl_4651_, 2);
lean_inc(v_v_4656_);
v_l_4657_ = lean_ctor_get(v_impl_4651_, 3);
lean_inc(v_l_4657_);
v_r_4658_ = lean_ctor_get(v_impl_4651_, 4);
lean_inc(v_r_4658_);
v___x_4659_ = lean_unsigned_to_nat(3u);
v___x_4660_ = lean_nat_mul(v___x_4659_, v_size_4653_);
v___x_4661_ = lean_nat_dec_lt(v___x_4660_, v_size_4654_);
lean_dec(v___x_4660_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
lean_dec(v_r_4658_);
lean_dec(v_l_4657_);
lean_dec(v_v_4656_);
lean_dec(v_k_4655_);
v___x_4662_ = lean_nat_add(v___x_4652_, v_size_4653_);
v___x_4663_ = lean_nat_add(v___x_4662_, v_size_4654_);
lean_dec(v_size_4654_);
lean_dec(v___x_4662_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_impl_4651_);
lean_ctor_set(v___x_4647_, 0, v___x_4663_);
v___x_4665_ = v___x_4647_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v_impl_4651_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
else
{
lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4730_; 
v_isSharedCheck_4730_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4730_ == 0)
{
lean_object* v_unused_4731_; lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; 
v_unused_4731_ = lean_ctor_get(v_impl_4651_, 4);
lean_dec(v_unused_4731_);
v_unused_4732_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_impl_4651_, 2);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_impl_4651_, 1);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4735_);
v___x_4668_ = v_impl_4651_;
v_isShared_4669_ = v_isSharedCheck_4730_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v_impl_4651_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4730_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v_size_4670_; lean_object* v_k_4671_; lean_object* v_v_4672_; lean_object* v_l_4673_; lean_object* v_r_4674_; lean_object* v_size_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_size_4670_ = lean_ctor_get(v_l_4657_, 0);
v_k_4671_ = lean_ctor_get(v_l_4657_, 1);
v_v_4672_ = lean_ctor_get(v_l_4657_, 2);
v_l_4673_ = lean_ctor_get(v_l_4657_, 3);
v_r_4674_ = lean_ctor_get(v_l_4657_, 4);
v_size_4675_ = lean_ctor_get(v_r_4658_, 0);
v___x_4676_ = lean_unsigned_to_nat(2u);
v___x_4677_ = lean_nat_mul(v___x_4676_, v_size_4675_);
v___x_4678_ = lean_nat_dec_lt(v_size_4670_, v___x_4677_);
lean_dec(v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4706_; 
lean_inc(v_r_4674_);
lean_inc(v_l_4673_);
lean_inc(v_v_4672_);
lean_inc(v_k_4671_);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_l_4657_);
if (v_isSharedCheck_4706_ == 0)
{
lean_object* v_unused_4707_; lean_object* v_unused_4708_; lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; 
v_unused_4707_ = lean_ctor_get(v_l_4657_, 4);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_l_4657_, 3);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_l_4657_, 2);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_l_4657_, 1);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_l_4657_, 0);
lean_dec(v_unused_4711_);
v___x_4680_ = v_l_4657_;
v_isShared_4681_ = v_isSharedCheck_4706_;
goto v_resetjp_4679_;
}
else
{
lean_dec(v_l_4657_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4706_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4696_; 
v___x_4682_ = lean_nat_add(v___x_4652_, v_size_4653_);
v___x_4683_ = lean_nat_add(v___x_4682_, v_size_4654_);
lean_dec(v_size_4654_);
if (lean_obj_tag(v_l_4673_) == 0)
{
lean_object* v_size_4704_; 
v_size_4704_ = lean_ctor_get(v_l_4673_, 0);
lean_inc(v_size_4704_);
v___y_4696_ = v_size_4704_;
goto v___jp_4695_;
}
else
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_unsigned_to_nat(0u);
v___y_4696_ = v___x_4705_;
goto v___jp_4695_;
}
v___jp_4684_:
{
lean_object* v___x_4688_; lean_object* v___x_4690_; 
v___x_4688_ = lean_nat_add(v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec(v___y_4686_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set(v___x_4680_, 4, v_r_4658_);
lean_ctor_set(v___x_4680_, 3, v_r_4674_);
lean_ctor_set(v___x_4680_, 2, v_v_4656_);
lean_ctor_set(v___x_4680_, 1, v_k_4655_);
lean_ctor_set(v___x_4680_, 0, v___x_4688_);
v___x_4690_ = v___x_4680_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4655_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4656_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v_r_4674_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v_r_4658_);
v___x_4690_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4692_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v___x_4690_);
lean_ctor_set(v___x_4668_, 3, v___y_4685_);
lean_ctor_set(v___x_4668_, 2, v_v_4672_);
lean_ctor_set(v___x_4668_, 1, v_k_4671_);
lean_ctor_set(v___x_4668_, 0, v___x_4683_);
v___x_4692_ = v___x_4668_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4683_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_k_4671_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_v_4672_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v___y_4685_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
v___jp_4695_:
{
lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4697_ = lean_nat_add(v___x_4682_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec(v___x_4682_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_l_4673_);
lean_ctor_set(v___x_4647_, 0, v___x_4697_);
v___x_4699_ = v___x_4647_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v_l_4673_);
v___x_4699_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_nat_add(v___x_4652_, v_size_4675_);
if (lean_obj_tag(v_r_4674_) == 0)
{
lean_object* v_size_4701_; 
v_size_4701_ = lean_ctor_get(v_r_4674_, 0);
lean_inc(v_size_4701_);
v___y_4685_ = v___x_4699_;
v___y_4686_ = v___x_4700_;
v___y_4687_ = v_size_4701_;
goto v___jp_4684_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___y_4685_ = v___x_4699_;
v___y_4686_ = v___x_4700_;
v___y_4687_ = v___x_4702_;
goto v___jp_4684_;
}
}
}
}
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
lean_del_object(v___x_4647_);
v___x_4712_ = lean_nat_add(v___x_4652_, v_size_4653_);
v___x_4713_ = lean_nat_add(v___x_4712_, v_size_4654_);
lean_dec(v_size_4654_);
v___x_4714_ = lean_nat_add(v___x_4712_, v_size_4670_);
lean_dec(v___x_4712_);
lean_inc_ref(v_l_4644_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v_l_4657_);
lean_ctor_set(v___x_4668_, 3, v_l_4644_);
lean_ctor_set(v___x_4668_, 2, v_v_4643_);
lean_ctor_set(v___x_4668_, 1, v_k_4642_);
lean_ctor_set(v___x_4668_, 0, v___x_4714_);
v___x_4716_ = v___x_4668_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4729_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4729_, 4, v_l_4657_);
v___x_4716_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
v_isSharedCheck_4723_ = !lean_is_exclusive(v_l_4644_);
if (v_isSharedCheck_4723_ == 0)
{
lean_object* v_unused_4724_; lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; 
v_unused_4724_ = lean_ctor_get(v_l_4644_, 4);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_l_4644_, 3);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_l_4644_, 2);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_l_4644_, 1);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_l_4644_, 0);
lean_dec(v_unused_4728_);
v___x_4718_ = v_l_4644_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_dec(v_l_4644_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 4, v_r_4658_);
lean_ctor_set(v___x_4718_, 3, v___x_4716_);
lean_ctor_set(v___x_4718_, 2, v_v_4656_);
lean_ctor_set(v___x_4718_, 1, v_k_4655_);
lean_ctor_set(v___x_4718_, 0, v___x_4713_);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_k_4655_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_v_4656_);
lean_ctor_set(v_reuseFailAlloc_4722_, 3, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4722_, 4, v_r_4658_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4736_; 
v_l_4736_ = lean_ctor_get(v_impl_4651_, 3);
lean_inc(v_l_4736_);
if (lean_obj_tag(v_l_4736_) == 0)
{
lean_object* v_r_4737_; lean_object* v_k_4738_; lean_object* v_v_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4762_; 
v_r_4737_ = lean_ctor_get(v_impl_4651_, 4);
v_k_4738_ = lean_ctor_get(v_impl_4651_, 1);
v_v_4739_ = lean_ctor_get(v_impl_4651_, 2);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4762_ == 0)
{
lean_object* v_unused_4763_; lean_object* v_unused_4764_; 
v_unused_4763_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4763_);
v_unused_4764_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4764_);
v___x_4741_ = v_impl_4651_;
v_isShared_4742_ = v_isSharedCheck_4762_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_r_4737_);
lean_inc(v_v_4739_);
lean_inc(v_k_4738_);
lean_dec(v_impl_4651_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4762_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v_k_4743_; lean_object* v_v_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4758_; 
v_k_4743_ = lean_ctor_get(v_l_4736_, 1);
v_v_4744_ = lean_ctor_get(v_l_4736_, 2);
v_isSharedCheck_4758_ = !lean_is_exclusive(v_l_4736_);
if (v_isSharedCheck_4758_ == 0)
{
lean_object* v_unused_4759_; lean_object* v_unused_4760_; lean_object* v_unused_4761_; 
v_unused_4759_ = lean_ctor_get(v_l_4736_, 4);
lean_dec(v_unused_4759_);
v_unused_4760_ = lean_ctor_get(v_l_4736_, 3);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_l_4736_, 0);
lean_dec(v_unused_4761_);
v___x_4746_ = v_l_4736_;
v_isShared_4747_ = v_isSharedCheck_4758_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_v_4744_);
lean_inc(v_k_4743_);
lean_dec(v_l_4736_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4758_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4748_; lean_object* v___x_4750_; 
v___x_4748_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4737_, 2);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 4, v_r_4737_);
lean_ctor_set(v___x_4746_, 3, v_r_4737_);
lean_ctor_set(v___x_4746_, 2, v_v_4643_);
lean_ctor_set(v___x_4746_, 1, v_k_4642_);
lean_ctor_set(v___x_4746_, 0, v___x_4652_);
v___x_4750_ = v___x_4746_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4757_, 3, v_r_4737_);
lean_ctor_set(v_reuseFailAlloc_4757_, 4, v_r_4737_);
v___x_4750_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4752_; 
lean_inc(v_r_4737_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 3, v_r_4737_);
lean_ctor_set(v___x_4741_, 0, v___x_4652_);
v___x_4752_ = v___x_4741_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_k_4738_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_v_4739_);
lean_ctor_set(v_reuseFailAlloc_4756_, 3, v_r_4737_);
lean_ctor_set(v_reuseFailAlloc_4756_, 4, v_r_4737_);
v___x_4752_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4754_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4752_);
lean_ctor_set(v___x_4647_, 3, v___x_4750_);
lean_ctor_set(v___x_4647_, 2, v_v_4744_);
lean_ctor_set(v___x_4647_, 1, v_k_4743_);
lean_ctor_set(v___x_4647_, 0, v___x_4748_);
v___x_4754_ = v___x_4647_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4748_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_k_4743_);
lean_ctor_set(v_reuseFailAlloc_4755_, 2, v_v_4744_);
lean_ctor_set(v_reuseFailAlloc_4755_, 3, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4755_, 4, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
}
else
{
lean_object* v_r_4765_; 
v_r_4765_ = lean_ctor_get(v_impl_4651_, 4);
lean_inc(v_r_4765_);
if (lean_obj_tag(v_r_4765_) == 0)
{
lean_object* v_k_4766_; lean_object* v_v_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4778_; 
v_k_4766_ = lean_ctor_get(v_impl_4651_, 1);
v_v_4767_ = lean_ctor_get(v_impl_4651_, 2);
v_isSharedCheck_4778_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4778_ == 0)
{
lean_object* v_unused_4779_; lean_object* v_unused_4780_; lean_object* v_unused_4781_; 
v_unused_4779_ = lean_ctor_get(v_impl_4651_, 4);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4781_);
v___x_4769_ = v_impl_4651_;
v_isShared_4770_ = v_isSharedCheck_4778_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_v_4767_);
lean_inc(v_k_4766_);
lean_dec(v_impl_4651_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4778_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___x_4773_; 
v___x_4771_ = lean_unsigned_to_nat(3u);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 4, v_l_4736_);
lean_ctor_set(v___x_4769_, 2, v_v_4643_);
lean_ctor_set(v___x_4769_, 1, v_k_4642_);
lean_ctor_set(v___x_4769_, 0, v___x_4652_);
v___x_4773_ = v___x_4769_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v_l_4736_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_l_4736_);
v___x_4773_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
lean_object* v___x_4775_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_r_4765_);
lean_ctor_set(v___x_4647_, 3, v___x_4773_);
lean_ctor_set(v___x_4647_, 2, v_v_4767_);
lean_ctor_set(v___x_4647_, 1, v_k_4766_);
lean_ctor_set(v___x_4647_, 0, v___x_4771_);
v___x_4775_ = v___x_4647_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_k_4766_);
lean_ctor_set(v_reuseFailAlloc_4776_, 2, v_v_4767_);
lean_ctor_set(v_reuseFailAlloc_4776_, 3, v___x_4773_);
lean_ctor_set(v_reuseFailAlloc_4776_, 4, v_r_4765_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4782_ = lean_unsigned_to_nat(2u);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_impl_4651_);
lean_ctor_set(v___x_4647_, 3, v_r_4765_);
lean_ctor_set(v___x_4647_, 0, v___x_4782_);
v___x_4784_ = v___x_4647_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_r_4765_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_impl_4651_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
else
{
lean_object* v___x_4787_; 
lean_dec(v_v_4643_);
lean_dec(v_k_4642_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 2, v_v_4639_);
lean_ctor_set(v___x_4647_, 1, v_k_4638_);
v___x_4787_ = v___x_4647_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_size_4641_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_k_4638_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_v_4639_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_r_4645_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
else
{
lean_object* v_impl_4789_; lean_object* v___x_4790_; 
lean_dec(v_size_4641_);
v_impl_4789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4638_, v_v_4639_, v_l_4644_);
v___x_4790_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4645_) == 0)
{
lean_object* v_size_4791_; lean_object* v_size_4792_; lean_object* v_k_4793_; lean_object* v_v_4794_; lean_object* v_l_4795_; lean_object* v_r_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; 
v_size_4791_ = lean_ctor_get(v_r_4645_, 0);
v_size_4792_ = lean_ctor_get(v_impl_4789_, 0);
lean_inc(v_size_4792_);
v_k_4793_ = lean_ctor_get(v_impl_4789_, 1);
lean_inc(v_k_4793_);
v_v_4794_ = lean_ctor_get(v_impl_4789_, 2);
lean_inc(v_v_4794_);
v_l_4795_ = lean_ctor_get(v_impl_4789_, 3);
lean_inc(v_l_4795_);
v_r_4796_ = lean_ctor_get(v_impl_4789_, 4);
lean_inc(v_r_4796_);
v___x_4797_ = lean_unsigned_to_nat(3u);
v___x_4798_ = lean_nat_mul(v___x_4797_, v_size_4791_);
v___x_4799_ = lean_nat_dec_lt(v___x_4798_, v_size_4792_);
lean_dec(v___x_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4803_; 
lean_dec(v_r_4796_);
lean_dec(v_l_4795_);
lean_dec(v_v_4794_);
lean_dec(v_k_4793_);
v___x_4800_ = lean_nat_add(v___x_4790_, v_size_4792_);
lean_dec(v_size_4792_);
v___x_4801_ = lean_nat_add(v___x_4800_, v_size_4791_);
lean_dec(v___x_4800_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 3, v_impl_4789_);
lean_ctor_set(v___x_4647_, 0, v___x_4801_);
v___x_4803_ = v___x_4647_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4804_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4804_, 3, v_impl_4789_);
lean_ctor_set(v_reuseFailAlloc_4804_, 4, v_r_4645_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
else
{
lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4870_; 
v_isSharedCheck_4870_ = !lean_is_exclusive(v_impl_4789_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; lean_object* v_unused_4875_; 
v_unused_4871_ = lean_ctor_get(v_impl_4789_, 4);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_impl_4789_, 3);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_impl_4789_, 2);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_impl_4789_, 1);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_impl_4789_, 0);
lean_dec(v_unused_4875_);
v___x_4806_ = v_impl_4789_;
v_isShared_4807_ = v_isSharedCheck_4870_;
goto v_resetjp_4805_;
}
else
{
lean_dec(v_impl_4789_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4870_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v_size_4808_; lean_object* v_size_4809_; lean_object* v_k_4810_; lean_object* v_v_4811_; lean_object* v_l_4812_; lean_object* v_r_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; 
v_size_4808_ = lean_ctor_get(v_l_4795_, 0);
v_size_4809_ = lean_ctor_get(v_r_4796_, 0);
v_k_4810_ = lean_ctor_get(v_r_4796_, 1);
v_v_4811_ = lean_ctor_get(v_r_4796_, 2);
v_l_4812_ = lean_ctor_get(v_r_4796_, 3);
v_r_4813_ = lean_ctor_get(v_r_4796_, 4);
v___x_4814_ = lean_unsigned_to_nat(2u);
v___x_4815_ = lean_nat_mul(v___x_4814_, v_size_4808_);
v___x_4816_ = lean_nat_dec_lt(v_size_4809_, v___x_4815_);
lean_dec(v___x_4815_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4845_; 
lean_inc(v_r_4813_);
lean_inc(v_l_4812_);
lean_inc(v_v_4811_);
lean_inc(v_k_4810_);
v_isSharedCheck_4845_ = !lean_is_exclusive(v_r_4796_);
if (v_isSharedCheck_4845_ == 0)
{
lean_object* v_unused_4846_; lean_object* v_unused_4847_; lean_object* v_unused_4848_; lean_object* v_unused_4849_; lean_object* v_unused_4850_; 
v_unused_4846_ = lean_ctor_get(v_r_4796_, 4);
lean_dec(v_unused_4846_);
v_unused_4847_ = lean_ctor_get(v_r_4796_, 3);
lean_dec(v_unused_4847_);
v_unused_4848_ = lean_ctor_get(v_r_4796_, 2);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_r_4796_, 1);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_r_4796_, 0);
lean_dec(v_unused_4850_);
v___x_4818_ = v_r_4796_;
v_isShared_4819_ = v_isSharedCheck_4845_;
goto v_resetjp_4817_;
}
else
{
lean_dec(v_r_4796_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4845_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___y_4823_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___x_4833_; lean_object* v___y_4835_; 
v___x_4820_ = lean_nat_add(v___x_4790_, v_size_4792_);
lean_dec(v_size_4792_);
v___x_4821_ = lean_nat_add(v___x_4820_, v_size_4791_);
lean_dec(v___x_4820_);
v___x_4833_ = lean_nat_add(v___x_4790_, v_size_4808_);
if (lean_obj_tag(v_l_4812_) == 0)
{
lean_object* v_size_4843_; 
v_size_4843_ = lean_ctor_get(v_l_4812_, 0);
lean_inc(v_size_4843_);
v___y_4835_ = v_size_4843_;
goto v___jp_4834_;
}
else
{
lean_object* v___x_4844_; 
v___x_4844_ = lean_unsigned_to_nat(0u);
v___y_4835_ = v___x_4844_;
goto v___jp_4834_;
}
v___jp_4822_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_nat_add(v___y_4823_, v___y_4825_);
lean_dec(v___y_4825_);
lean_dec(v___y_4823_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 4, v_r_4645_);
lean_ctor_set(v___x_4818_, 3, v_r_4813_);
lean_ctor_set(v___x_4818_, 2, v_v_4643_);
lean_ctor_set(v___x_4818_, 1, v_k_4642_);
lean_ctor_set(v___x_4818_, 0, v___x_4826_);
v___x_4828_ = v___x_4818_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v_r_4813_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v_r_4645_);
v___x_4828_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4830_; 
if (v_isShared_4807_ == 0)
{
lean_ctor_set(v___x_4806_, 4, v___x_4828_);
lean_ctor_set(v___x_4806_, 3, v___y_4824_);
lean_ctor_set(v___x_4806_, 2, v_v_4811_);
lean_ctor_set(v___x_4806_, 1, v_k_4810_);
lean_ctor_set(v___x_4806_, 0, v___x_4821_);
v___x_4830_ = v___x_4806_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_k_4810_);
lean_ctor_set(v_reuseFailAlloc_4831_, 2, v_v_4811_);
lean_ctor_set(v_reuseFailAlloc_4831_, 3, v___y_4824_);
lean_ctor_set(v_reuseFailAlloc_4831_, 4, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
v___jp_4834_:
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4836_ = lean_nat_add(v___x_4833_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec(v___x_4833_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_l_4812_);
lean_ctor_set(v___x_4647_, 3, v_l_4795_);
lean_ctor_set(v___x_4647_, 2, v_v_4794_);
lean_ctor_set(v___x_4647_, 1, v_k_4793_);
lean_ctor_set(v___x_4647_, 0, v___x_4836_);
v___x_4838_ = v___x_4647_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_k_4793_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v_v_4794_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v_l_4795_);
lean_ctor_set(v_reuseFailAlloc_4842_, 4, v_l_4812_);
v___x_4838_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_nat_add(v___x_4790_, v_size_4791_);
if (lean_obj_tag(v_r_4813_) == 0)
{
lean_object* v_size_4840_; 
v_size_4840_ = lean_ctor_get(v_r_4813_, 0);
lean_inc(v_size_4840_);
v___y_4823_ = v___x_4839_;
v___y_4824_ = v___x_4838_;
v___y_4825_ = v_size_4840_;
goto v___jp_4822_;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___y_4823_ = v___x_4839_;
v___y_4824_ = v___x_4838_;
v___y_4825_ = v___x_4841_;
goto v___jp_4822_;
}
}
}
}
}
else
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
lean_del_object(v___x_4647_);
v___x_4851_ = lean_nat_add(v___x_4790_, v_size_4792_);
lean_dec(v_size_4792_);
v___x_4852_ = lean_nat_add(v___x_4851_, v_size_4791_);
lean_dec(v___x_4851_);
v___x_4853_ = lean_nat_add(v___x_4790_, v_size_4791_);
v___x_4854_ = lean_nat_add(v___x_4853_, v_size_4809_);
lean_dec(v___x_4853_);
lean_inc_ref(v_r_4645_);
if (v_isShared_4807_ == 0)
{
lean_ctor_set(v___x_4806_, 4, v_r_4645_);
lean_ctor_set(v___x_4806_, 3, v_r_4796_);
lean_ctor_set(v___x_4806_, 2, v_v_4643_);
lean_ctor_set(v___x_4806_, 1, v_k_4642_);
lean_ctor_set(v___x_4806_, 0, v___x_4854_);
v___x_4856_ = v___x_4806_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_r_4796_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_r_4645_);
v___x_4856_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
v_isSharedCheck_4863_ = !lean_is_exclusive(v_r_4645_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; lean_object* v_unused_4868_; 
v_unused_4864_ = lean_ctor_get(v_r_4645_, 4);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_r_4645_, 3);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_r_4645_, 2);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_r_4645_, 1);
lean_dec(v_unused_4867_);
v_unused_4868_ = lean_ctor_get(v_r_4645_, 0);
lean_dec(v_unused_4868_);
v___x_4858_ = v_r_4645_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_dec(v_r_4645_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 4, v___x_4856_);
lean_ctor_set(v___x_4858_, 3, v_l_4795_);
lean_ctor_set(v___x_4858_, 2, v_v_4794_);
lean_ctor_set(v___x_4858_, 1, v_k_4793_);
lean_ctor_set(v___x_4858_, 0, v___x_4852_);
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_k_4793_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_v_4794_);
lean_ctor_set(v_reuseFailAlloc_4862_, 3, v_l_4795_);
lean_ctor_set(v_reuseFailAlloc_4862_, 4, v___x_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4876_; 
v_l_4876_ = lean_ctor_get(v_impl_4789_, 3);
lean_inc(v_l_4876_);
if (lean_obj_tag(v_l_4876_) == 0)
{
lean_object* v_r_4877_; lean_object* v_k_4878_; lean_object* v_v_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4890_; 
v_r_4877_ = lean_ctor_get(v_impl_4789_, 4);
v_k_4878_ = lean_ctor_get(v_impl_4789_, 1);
v_v_4879_ = lean_ctor_get(v_impl_4789_, 2);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_impl_4789_);
if (v_isSharedCheck_4890_ == 0)
{
lean_object* v_unused_4891_; lean_object* v_unused_4892_; 
v_unused_4891_ = lean_ctor_get(v_impl_4789_, 3);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_impl_4789_, 0);
lean_dec(v_unused_4892_);
v___x_4881_ = v_impl_4789_;
v_isShared_4882_ = v_isSharedCheck_4890_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_r_4877_);
lean_inc(v_v_4879_);
lean_inc(v_k_4878_);
lean_dec(v_impl_4789_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4890_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4883_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4877_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 3, v_r_4877_);
lean_ctor_set(v___x_4881_, 2, v_v_4643_);
lean_ctor_set(v___x_4881_, 1, v_k_4642_);
lean_ctor_set(v___x_4881_, 0, v___x_4790_);
v___x_4885_ = v___x_4881_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_r_4877_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v_r_4877_);
v___x_4885_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_object* v___x_4887_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4885_);
lean_ctor_set(v___x_4647_, 3, v_l_4876_);
lean_ctor_set(v___x_4647_, 2, v_v_4879_);
lean_ctor_set(v___x_4647_, 1, v_k_4878_);
lean_ctor_set(v___x_4647_, 0, v___x_4883_);
v___x_4887_ = v___x_4647_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_k_4878_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_v_4879_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v_l_4876_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
lean_object* v_r_4893_; 
v_r_4893_ = lean_ctor_get(v_impl_4789_, 4);
lean_inc(v_r_4893_);
if (lean_obj_tag(v_r_4893_) == 0)
{
lean_object* v_k_4894_; lean_object* v_v_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4918_; 
v_k_4894_ = lean_ctor_get(v_impl_4789_, 1);
v_v_4895_ = lean_ctor_get(v_impl_4789_, 2);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_impl_4789_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; lean_object* v_unused_4920_; lean_object* v_unused_4921_; 
v_unused_4919_ = lean_ctor_get(v_impl_4789_, 4);
lean_dec(v_unused_4919_);
v_unused_4920_ = lean_ctor_get(v_impl_4789_, 3);
lean_dec(v_unused_4920_);
v_unused_4921_ = lean_ctor_get(v_impl_4789_, 0);
lean_dec(v_unused_4921_);
v___x_4897_ = v_impl_4789_;
v_isShared_4898_ = v_isSharedCheck_4918_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_v_4895_);
lean_inc(v_k_4894_);
lean_dec(v_impl_4789_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4918_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v_k_4899_; lean_object* v_v_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4914_; 
v_k_4899_ = lean_ctor_get(v_r_4893_, 1);
v_v_4900_ = lean_ctor_get(v_r_4893_, 2);
v_isSharedCheck_4914_ = !lean_is_exclusive(v_r_4893_);
if (v_isSharedCheck_4914_ == 0)
{
lean_object* v_unused_4915_; lean_object* v_unused_4916_; lean_object* v_unused_4917_; 
v_unused_4915_ = lean_ctor_get(v_r_4893_, 4);
lean_dec(v_unused_4915_);
v_unused_4916_ = lean_ctor_get(v_r_4893_, 3);
lean_dec(v_unused_4916_);
v_unused_4917_ = lean_ctor_get(v_r_4893_, 0);
lean_dec(v_unused_4917_);
v___x_4902_ = v_r_4893_;
v_isShared_4903_ = v_isSharedCheck_4914_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_v_4900_);
lean_inc(v_k_4899_);
lean_dec(v_r_4893_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4914_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4904_ = lean_unsigned_to_nat(3u);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 4, v_l_4876_);
lean_ctor_set(v___x_4902_, 3, v_l_4876_);
lean_ctor_set(v___x_4902_, 2, v_v_4895_);
lean_ctor_set(v___x_4902_, 1, v_k_4894_);
lean_ctor_set(v___x_4902_, 0, v___x_4790_);
v___x_4906_ = v___x_4902_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_k_4894_);
lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_v_4895_);
lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_l_4876_);
lean_ctor_set(v_reuseFailAlloc_4913_, 4, v_l_4876_);
v___x_4906_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4908_; 
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 4, v_l_4876_);
lean_ctor_set(v___x_4897_, 2, v_v_4643_);
lean_ctor_set(v___x_4897_, 1, v_k_4642_);
lean_ctor_set(v___x_4897_, 0, v___x_4790_);
v___x_4908_ = v___x_4897_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v_l_4876_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v_l_4876_);
v___x_4908_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4910_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4908_);
lean_ctor_set(v___x_4647_, 3, v___x_4906_);
lean_ctor_set(v___x_4647_, 2, v_v_4900_);
lean_ctor_set(v___x_4647_, 1, v_k_4899_);
lean_ctor_set(v___x_4647_, 0, v___x_4904_);
v___x_4910_ = v___x_4647_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_k_4899_);
lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_v_4900_);
lean_ctor_set(v_reuseFailAlloc_4911_, 3, v___x_4906_);
lean_ctor_set(v_reuseFailAlloc_4911_, 4, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4924_; 
v___x_4922_ = lean_unsigned_to_nat(2u);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_r_4893_);
lean_ctor_set(v___x_4647_, 3, v_impl_4789_);
lean_ctor_set(v___x_4647_, 0, v___x_4922_);
v___x_4924_ = v___x_4647_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4925_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4925_, 3, v_impl_4789_);
lean_ctor_set(v_reuseFailAlloc_4925_, 4, v_r_4893_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_unsigned_to_nat(1u);
v___x_4928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
lean_ctor_set(v___x_4928_, 1, v_k_4638_);
lean_ctor_set(v___x_4928_, 2, v_v_4639_);
lean_ctor_set(v___x_4928_, 3, v_t_4640_);
lean_ctor_set(v___x_4928_, 4, v_t_4640_);
return v___x_4928_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_4929_, lean_object* v_t_4930_){
_start:
{
if (lean_obj_tag(v_t_4930_) == 0)
{
lean_object* v_k_4931_; lean_object* v_l_4932_; lean_object* v_r_4933_; uint8_t v___x_4934_; 
v_k_4931_ = lean_ctor_get(v_t_4930_, 1);
v_l_4932_ = lean_ctor_get(v_t_4930_, 3);
v_r_4933_ = lean_ctor_get(v_t_4930_, 4);
v___x_4934_ = lean_nat_dec_lt(v_k_4931_, v_k_4929_);
if (v___x_4934_ == 0)
{
uint8_t v___x_4935_; 
v___x_4935_ = lean_nat_dec_eq(v_k_4931_, v_k_4929_);
if (v___x_4935_ == 0)
{
v_t_4930_ = v_r_4933_;
goto _start;
}
else
{
return v___x_4935_;
}
}
else
{
v_t_4930_ = v_l_4932_;
goto _start;
}
}
else
{
uint8_t v___x_4938_; 
v___x_4938_ = 0;
return v___x_4938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_4939_, lean_object* v_t_4940_){
_start:
{
uint8_t v_res_4941_; lean_object* v_r_4942_; 
v_res_4941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4939_, v_t_4940_);
lean_dec(v_t_4940_);
lean_dec(v_k_4939_);
v_r_4942_ = lean_box(v_res_4941_);
return v_r_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_4943_, lean_object* v_e_4944_){
_start:
{
lean_object* v_defaultInstances_4945_; lean_object* v_priorities_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4973_; 
v_defaultInstances_4945_ = lean_ctor_get(v_d_4943_, 0);
v_priorities_4946_ = lean_ctor_get(v_d_4943_, 1);
v_isSharedCheck_4973_ = !lean_is_exclusive(v_d_4943_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4948_ = v_d_4943_;
v_isShared_4949_ = v_isSharedCheck_4973_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_priorities_4946_);
lean_inc(v_defaultInstances_4945_);
lean_dec(v_d_4943_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4973_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v_className_4950_; lean_object* v_instanceName_4951_; lean_object* v_priority_4952_; lean_object* v___y_4954_; uint8_t v___x_4970_; 
v_className_4950_ = lean_ctor_get(v_e_4944_, 0);
lean_inc(v_className_4950_);
v_instanceName_4951_ = lean_ctor_get(v_e_4944_, 1);
lean_inc(v_instanceName_4951_);
v_priority_4952_ = lean_ctor_get(v_e_4944_, 2);
lean_inc(v_priority_4952_);
lean_dec_ref(v_e_4944_);
v___x_4970_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_4952_, v_priorities_4946_);
if (v___x_4970_ == 0)
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_box(0);
lean_inc(v_priority_4952_);
v___x_4972_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_4952_, v___x_4971_, v_priorities_4946_);
v___y_4954_ = v___x_4972_;
goto v___jp_4953_;
}
else
{
v___y_4954_ = v_priorities_4946_;
goto v___jp_4953_;
}
v___jp_4953_:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_4945_, v_className_4950_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4961_; 
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v_instanceName_4951_);
lean_ctor_set(v___x_4956_, 1, v_priority_4952_);
v___x_4957_ = lean_box(0);
v___x_4958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4950_, v___x_4958_, v_defaultInstances_4945_);
if (v_isShared_4949_ == 0)
{
lean_ctor_set(v___x_4948_, 1, v___y_4954_);
lean_ctor_set(v___x_4948_, 0, v___x_4959_);
v___x_4961_ = v___x_4948_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v___y_4954_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
else
{
lean_object* v_val_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; 
v_val_4963_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_val_4963_);
lean_dec_ref(v___x_4955_);
v___x_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_instanceName_4951_);
lean_ctor_set(v___x_4964_, 1, v_priority_4952_);
v___x_4965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
lean_ctor_set(v___x_4965_, 1, v_val_4963_);
v___x_4966_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4950_, v___x_4965_, v_defaultInstances_4945_);
if (v_isShared_4949_ == 0)
{
lean_ctor_set(v___x_4948_, 1, v___y_4954_);
lean_ctor_set(v___x_4948_, 0, v___x_4966_);
v___x_4968_ = v___x_4948_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4966_);
lean_ctor_set(v_reuseFailAlloc_4969_, 1, v___y_4954_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_4974_, lean_object* v_k_4975_, lean_object* v_t_4976_){
_start:
{
uint8_t v___x_4977_; 
v___x_4977_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4975_, v_t_4976_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_4978_, lean_object* v_k_4979_, lean_object* v_t_4980_){
_start:
{
uint8_t v_res_4981_; lean_object* v_r_4982_; 
v_res_4981_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_4978_, v_k_4979_, v_t_4980_);
lean_dec(v_t_4980_);
lean_dec(v_k_4979_);
v_r_4982_ = lean_box(v_res_4981_);
return v_r_4982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_4983_, lean_object* v_k_4984_, lean_object* v_v_4985_, lean_object* v_t_4986_, lean_object* v_hl_4987_){
_start:
{
lean_object* v___x_4988_; 
v___x_4988_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4984_, v_v_4985_, v_t_4986_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_4989_){
_start:
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_array_mk(v_es_4989_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4991_, size_t v_i_4992_, size_t v_stop_4993_, lean_object* v_b_4994_){
_start:
{
uint8_t v___x_4995_; 
v___x_4995_ = lean_usize_dec_eq(v_i_4992_, v_stop_4993_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; size_t v___x_4998_; size_t v___x_4999_; 
v___x_4996_ = lean_array_uget_borrowed(v_as_4991_, v_i_4992_);
lean_inc(v___x_4996_);
v___x_4997_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_4994_, v___x_4996_);
v___x_4998_ = ((size_t)1ULL);
v___x_4999_ = lean_usize_add(v_i_4992_, v___x_4998_);
v_i_4992_ = v___x_4999_;
v_b_4994_ = v___x_4997_;
goto _start;
}
else
{
return v_b_4994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5001_, lean_object* v_i_5002_, lean_object* v_stop_5003_, lean_object* v_b_5004_){
_start:
{
size_t v_i_boxed_5005_; size_t v_stop_boxed_5006_; lean_object* v_res_5007_; 
v_i_boxed_5005_ = lean_unbox_usize(v_i_5002_);
lean_dec(v_i_5002_);
v_stop_boxed_5006_ = lean_unbox_usize(v_stop_5003_);
lean_dec(v_stop_5003_);
v_res_5007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_5001_, v_i_boxed_5005_, v_stop_boxed_5006_, v_b_5004_);
lean_dec_ref(v_as_5001_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_5008_, size_t v_i_5009_, size_t v_stop_5010_, lean_object* v_b_5011_){
_start:
{
lean_object* v___y_5013_; uint8_t v___x_5017_; 
v___x_5017_ = lean_usize_dec_eq(v_i_5009_, v_stop_5010_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; uint8_t v___x_5021_; 
v___x_5018_ = lean_array_uget_borrowed(v_as_5008_, v_i_5009_);
v___x_5019_ = lean_unsigned_to_nat(0u);
v___x_5020_ = lean_array_get_size(v___x_5018_);
v___x_5021_ = lean_nat_dec_lt(v___x_5019_, v___x_5020_);
if (v___x_5021_ == 0)
{
v___y_5013_ = v_b_5011_;
goto v___jp_5012_;
}
else
{
uint8_t v___x_5022_; 
v___x_5022_ = lean_nat_dec_le(v___x_5020_, v___x_5020_);
if (v___x_5022_ == 0)
{
if (v___x_5021_ == 0)
{
v___y_5013_ = v_b_5011_;
goto v___jp_5012_;
}
else
{
size_t v___x_5023_; size_t v___x_5024_; lean_object* v___x_5025_; 
v___x_5023_ = ((size_t)0ULL);
v___x_5024_ = lean_usize_of_nat(v___x_5020_);
v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5018_, v___x_5023_, v___x_5024_, v_b_5011_);
v___y_5013_ = v___x_5025_;
goto v___jp_5012_;
}
}
else
{
size_t v___x_5026_; size_t v___x_5027_; lean_object* v___x_5028_; 
v___x_5026_ = ((size_t)0ULL);
v___x_5027_ = lean_usize_of_nat(v___x_5020_);
v___x_5028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5018_, v___x_5026_, v___x_5027_, v_b_5011_);
v___y_5013_ = v___x_5028_;
goto v___jp_5012_;
}
}
}
else
{
return v_b_5011_;
}
v___jp_5012_:
{
size_t v___x_5014_; size_t v___x_5015_; 
v___x_5014_ = ((size_t)1ULL);
v___x_5015_ = lean_usize_add(v_i_5009_, v___x_5014_);
v_i_5009_ = v___x_5015_;
v_b_5011_ = v___y_5013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5029_, lean_object* v_i_5030_, lean_object* v_stop_5031_, lean_object* v_b_5032_){
_start:
{
size_t v_i_boxed_5033_; size_t v_stop_boxed_5034_; lean_object* v_res_5035_; 
v_i_boxed_5033_ = lean_unbox_usize(v_i_5030_);
lean_dec(v_i_5030_);
v_stop_boxed_5034_ = lean_unbox_usize(v_stop_5031_);
lean_dec(v_stop_5031_);
v_res_5035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5029_, v_i_boxed_5033_, v_stop_boxed_5034_, v_b_5032_);
lean_dec_ref(v_as_5029_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5036_, lean_object* v_as_5037_){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v___x_5038_ = lean_unsigned_to_nat(0u);
v___x_5039_ = lean_array_get_size(v_as_5037_);
v___x_5040_ = lean_nat_dec_lt(v___x_5038_, v___x_5039_);
if (v___x_5040_ == 0)
{
return v_initState_5036_;
}
else
{
uint8_t v___x_5041_; 
v___x_5041_ = lean_nat_dec_le(v___x_5039_, v___x_5039_);
if (v___x_5041_ == 0)
{
if (v___x_5040_ == 0)
{
return v_initState_5036_;
}
else
{
size_t v___x_5042_; size_t v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = ((size_t)0ULL);
v___x_5043_ = lean_usize_of_nat(v___x_5039_);
v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5037_, v___x_5042_, v___x_5043_, v_initState_5036_);
return v___x_5044_;
}
}
else
{
size_t v___x_5045_; size_t v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = ((size_t)0ULL);
v___x_5046_ = lean_usize_of_nat(v___x_5039_);
v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5037_, v___x_5045_, v___x_5046_, v_initState_5036_);
return v___x_5047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5048_, lean_object* v_as_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5048_, v_as_5049_);
lean_dec_ref(v_as_5049_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5051_){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5053_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5052_, v_es_5051_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5054_);
lean_dec_ref(v_es_5054_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5073_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5072_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v___x_5080_; lean_object* v_nextMacroScope_5081_; lean_object* v_ngen_5082_; lean_object* v_auxDeclNGen_5083_; lean_object* v_traceState_5084_; lean_object* v_messages_5085_; lean_object* v_infoState_5086_; lean_object* v_snapshotTasks_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5113_; 
v___x_5080_ = lean_st_ref_take(v___y_5078_);
v_nextMacroScope_5081_ = lean_ctor_get(v___x_5080_, 1);
v_ngen_5082_ = lean_ctor_get(v___x_5080_, 2);
v_auxDeclNGen_5083_ = lean_ctor_get(v___x_5080_, 3);
v_traceState_5084_ = lean_ctor_get(v___x_5080_, 4);
v_messages_5085_ = lean_ctor_get(v___x_5080_, 6);
v_infoState_5086_ = lean_ctor_get(v___x_5080_, 7);
v_snapshotTasks_5087_ = lean_ctor_get(v___x_5080_, 8);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5113_ == 0)
{
lean_object* v_unused_5114_; lean_object* v_unused_5115_; 
v_unused_5114_ = lean_ctor_get(v___x_5080_, 5);
lean_dec(v_unused_5114_);
v_unused_5115_ = lean_ctor_get(v___x_5080_, 0);
lean_dec(v_unused_5115_);
v___x_5089_ = v___x_5080_;
v_isShared_5090_ = v_isSharedCheck_5113_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_snapshotTasks_5087_);
lean_inc(v_infoState_5086_);
lean_inc(v_messages_5085_);
lean_inc(v_traceState_5084_);
lean_inc(v_auxDeclNGen_5083_);
lean_inc(v_ngen_5082_);
lean_inc(v_nextMacroScope_5081_);
lean_dec(v___x_5080_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5113_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5091_; lean_object* v___x_5093_; 
v___x_5091_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5090_ == 0)
{
lean_ctor_set(v___x_5089_, 5, v___x_5091_);
lean_ctor_set(v___x_5089_, 0, v_env_5076_);
v___x_5093_ = v___x_5089_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_env_5076_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_nextMacroScope_5081_);
lean_ctor_set(v_reuseFailAlloc_5112_, 2, v_ngen_5082_);
lean_ctor_set(v_reuseFailAlloc_5112_, 3, v_auxDeclNGen_5083_);
lean_ctor_set(v_reuseFailAlloc_5112_, 4, v_traceState_5084_);
lean_ctor_set(v_reuseFailAlloc_5112_, 5, v___x_5091_);
lean_ctor_set(v_reuseFailAlloc_5112_, 6, v_messages_5085_);
lean_ctor_set(v_reuseFailAlloc_5112_, 7, v_infoState_5086_);
lean_ctor_set(v_reuseFailAlloc_5112_, 8, v_snapshotTasks_5087_);
v___x_5093_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v_mctx_5096_; lean_object* v_zetaDeltaFVarIds_5097_; lean_object* v_postponed_5098_; lean_object* v_diag_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5110_; 
v___x_5094_ = lean_st_ref_set(v___y_5078_, v___x_5093_);
v___x_5095_ = lean_st_ref_take(v___y_5077_);
v_mctx_5096_ = lean_ctor_get(v___x_5095_, 0);
v_zetaDeltaFVarIds_5097_ = lean_ctor_get(v___x_5095_, 2);
v_postponed_5098_ = lean_ctor_get(v___x_5095_, 3);
v_diag_5099_ = lean_ctor_get(v___x_5095_, 4);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5110_ == 0)
{
lean_object* v_unused_5111_; 
v_unused_5111_ = lean_ctor_get(v___x_5095_, 1);
lean_dec(v_unused_5111_);
v___x_5101_ = v___x_5095_;
v_isShared_5102_ = v_isSharedCheck_5110_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_diag_5099_);
lean_inc(v_postponed_5098_);
lean_inc(v_zetaDeltaFVarIds_5097_);
lean_inc(v_mctx_5096_);
lean_dec(v___x_5095_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5110_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; lean_object* v___x_5105_; 
v___x_5103_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 1, v___x_5103_);
v___x_5105_ = v___x_5101_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_mctx_5096_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5103_);
lean_ctor_set(v_reuseFailAlloc_5109_, 2, v_zetaDeltaFVarIds_5097_);
lean_ctor_set(v_reuseFailAlloc_5109_, 3, v_postponed_5098_);
lean_ctor_set(v_reuseFailAlloc_5109_, 4, v_diag_5099_);
v___x_5105_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5106_ = lean_st_ref_set(v___y_5077_, v___x_5105_);
v___x_5107_ = lean_box(0);
v___x_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
return v___x_5108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5116_, v___y_5117_, v___y_5118_);
lean_dec(v___y_5118_);
lean_dec(v___y_5117_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5121_, v___y_5123_, v___y_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
return v_res_5134_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5137_ = l_Lean_stringToMessageData(v___x_5136_);
return v___x_5137_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5140_ = l_Lean_stringToMessageData(v___x_5139_);
return v___x_5140_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5142_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5143_ = l_Lean_stringToMessageData(v___x_5142_);
return v___x_5143_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5145_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5146_ = l_Lean_stringToMessageData(v___x_5145_);
return v___x_5146_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5149_ = l_Lean_stringToMessageData(v___x_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5150_, lean_object* v_prio_5151_, lean_object* v_x_5152_, lean_object* v_type_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l_Lean_Expr_getAppFn(v_type_5153_);
if (lean_obj_tag(v___x_5159_) == 4)
{
lean_object* v_declName_5160_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v___y_5164_; lean_object* v___y_5165_; lean_object* v___x_5175_; lean_object* v_env_5176_; uint8_t v___x_5177_; 
v_declName_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc_n(v_declName_5160_, 2);
lean_dec_ref(v___x_5159_);
v___x_5175_ = lean_st_ref_get(v___y_5157_);
v_env_5176_ = lean_ctor_get(v___x_5175_, 0);
lean_inc_ref(v_env_5176_);
lean_dec(v___x_5175_);
v___x_5177_ = lean_is_class(v_env_5176_, v_declName_5160_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; 
lean_dec(v_prio_5151_);
v___x_5178_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5179_ = l_Lean_MessageData_ofConstName(v_declName_5150_, v___x_5177_);
v___x_5180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5178_);
lean_ctor_set(v___x_5180_, 1, v___x_5179_);
v___x_5181_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5180_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
lean_inc(v_declName_5160_);
v___x_5183_ = l_Lean_MessageData_ofName(v_declName_5160_);
v___x_5184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5184_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = l_Lean_MessageData_ofConstName(v_declName_5160_, v___x_5177_);
v___x_5188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5186_);
lean_ctor_set(v___x_5188_, 1, v___x_5187_);
v___x_5189_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5188_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5190_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
return v___x_5191_;
}
else
{
v___y_5162_ = v___y_5154_;
v___y_5163_ = v___y_5155_;
v___y_5164_ = v___y_5156_;
v___y_5165_ = v___y_5157_;
goto v___jp_5161_;
}
v___jp_5161_:
{
lean_object* v___x_5166_; lean_object* v_env_5167_; lean_object* v___x_5168_; lean_object* v_toEnvExtension_5169_; lean_object* v_asyncMode_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5166_ = lean_st_ref_get(v___y_5165_);
v_env_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc_ref(v_env_5167_);
lean_dec(v___x_5166_);
v___x_5168_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5169_ = lean_ctor_get(v___x_5168_, 0);
v_asyncMode_5170_ = lean_ctor_get(v_toEnvExtension_5169_, 2);
v___x_5171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5171_, 0, v_declName_5160_);
lean_ctor_set(v___x_5171_, 1, v_declName_5150_);
lean_ctor_set(v___x_5171_, 2, v_prio_5151_);
v___x_5172_ = lean_box(0);
v___x_5173_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5168_, v_env_5167_, v___x_5171_, v_asyncMode_5170_, v___x_5172_);
v___x_5174_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5173_, v___y_5163_, v___y_5165_);
return v___x_5174_;
}
}
else
{
lean_object* v___x_5192_; uint8_t v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
lean_dec_ref(v___x_5159_);
lean_dec(v_prio_5151_);
v___x_5192_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5193_ = 0;
v___x_5194_ = l_Lean_MessageData_ofConstName(v_declName_5150_, v___x_5193_);
v___x_5195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5192_);
lean_ctor_set(v___x_5195_, 1, v___x_5194_);
v___x_5196_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5197_, 0, v___x_5195_);
lean_ctor_set(v___x_5197_, 1, v___x_5196_);
v___x_5198_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5197_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
return v___x_5198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5199_, lean_object* v_prio_5200_, lean_object* v_x_5201_, lean_object* v_type_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5199_, v_prio_5200_, v_x_5201_, v_type_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec_ref(v_type_5202_);
lean_dec_ref(v_x_5201_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5209_, lean_object* v_prio_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v___x_5216_; lean_object* v_env_5217_; uint8_t v___x_5218_; lean_object* v___x_5219_; 
v___x_5216_ = lean_st_ref_get(v_a_5214_);
v_env_5217_ = lean_ctor_get(v___x_5216_, 0);
lean_inc_ref(v_env_5217_);
lean_dec(v___x_5216_);
v___x_5218_ = 0;
lean_inc(v_declName_5209_);
v___x_5219_ = l_Lean_Environment_find_x3f(v_env_5217_, v_declName_5209_, v___x_5218_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_dec(v_prio_5210_);
v___x_5220_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5221_ = l_Lean_MessageData_ofConstName(v_declName_5209_, v___x_5218_);
v___x_5222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5220_);
lean_ctor_set(v___x_5222_, 1, v___x_5221_);
v___x_5223_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5222_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5224_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
return v___x_5225_;
}
else
{
lean_object* v_val_5226_; lean_object* v___f_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_val_5226_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_val_5226_);
lean_dec_ref(v___x_5219_);
v___f_5227_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5227_, 0, v_declName_5209_);
lean_closure_set(v___f_5227_, 1, v_prio_5210_);
v___x_5228_ = l_Lean_ConstantInfo_type(v_val_5226_);
lean_dec(v_val_5226_);
v___x_5229_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5228_, v___f_5227_, v___x_5218_, v___x_5218_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
return v___x_5229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5230_, lean_object* v_prio_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Meta_addDefaultInstance(v_declName_5230_, v_prio_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
lean_dec_ref(v_a_5232_);
return v_res_5237_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5239_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5240_ = l_Lean_stringToMessageData(v___x_5239_);
return v___x_5240_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5242_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5243_ = l_Lean_stringToMessageData(v___x_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5247_, uint8_t v_kind_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___y_5258_; 
v___x_5252_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5253_ = l_Lean_MessageData_ofName(v_name_5247_);
v___x_5254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5252_);
lean_ctor_set(v___x_5254_, 1, v___x_5253_);
v___x_5255_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5256_, 0, v___x_5254_);
lean_ctor_set(v___x_5256_, 1, v___x_5255_);
switch(v_kind_5248_)
{
case 0:
{
lean_object* v___x_5265_; 
v___x_5265_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5258_ = v___x_5265_;
goto v___jp_5257_;
}
case 1:
{
lean_object* v___x_5266_; 
v___x_5266_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5258_ = v___x_5266_;
goto v___jp_5257_;
}
default: 
{
lean_object* v___x_5267_; 
v___x_5267_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5258_ = v___x_5267_;
goto v___jp_5257_;
}
}
v___jp_5257_:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; 
lean_inc_ref(v___y_5258_);
v___x_5259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___y_5258_);
v___x_5260_ = l_Lean_MessageData_ofFormat(v___x_5259_);
v___x_5261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5256_);
lean_ctor_set(v___x_5261_, 1, v___x_5260_);
v___x_5262_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5261_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
v___x_5264_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5263_, v___y_5249_, v___y_5250_);
return v___x_5264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5268_, lean_object* v_kind_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
uint8_t v_kind_boxed_5273_; lean_object* v_res_5274_; 
v_kind_boxed_5273_ = lean_unbox(v_kind_5269_);
v_res_5274_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5268_, v_kind_boxed_5273_, v___y_5270_, v___y_5271_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5275_, lean_object* v___x_5276_, lean_object* v___x_5277_, lean_object* v_declName_5278_, lean_object* v_stx_5279_, uint8_t v_kind_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5284_ = lean_unsigned_to_nat(1u);
v___x_5285_ = l_Lean_Syntax_getArg(v_stx_5279_, v___x_5284_);
v___x_5286_ = l_Lean_getAttrParamOptPrio(v___x_5285_, v___y_5281_, v___y_5282_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v___y_5289_; lean_object* v___y_5290_; uint8_t v___x_5321_; uint8_t v___x_5322_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_a_5287_);
lean_dec_ref(v___x_5286_);
v___x_5321_ = 0;
v___x_5322_ = l_Lean_instBEqAttributeKind_beq(v_kind_5280_, v___x_5321_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
lean_dec(v_a_5287_);
lean_dec(v_declName_5278_);
lean_dec(v___x_5276_);
lean_dec(v___x_5275_);
v___x_5323_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5277_, v_kind_5280_, v___y_5281_, v___y_5282_);
return v___x_5323_;
}
else
{
lean_dec(v___x_5277_);
v___y_5289_ = v___y_5281_;
v___y_5290_ = v___y_5282_;
goto v___jp_5288_;
}
v___jp_5288_:
{
uint8_t v___x_5291_; uint8_t v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; size_t v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5291_ = 0;
v___x_5292_ = 1;
v___x_5293_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5294_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5295_ = lean_unsigned_to_nat(32u);
v___x_5296_ = lean_mk_empty_array_with_capacity(v___x_5295_);
v___x_5297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5298_ = ((size_t)5ULL);
lean_inc_n(v___x_5275_, 5);
v___x_5299_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5299_, 0, v___x_5297_);
lean_ctor_set(v___x_5299_, 1, v___x_5296_);
lean_ctor_set(v___x_5299_, 2, v___x_5275_);
lean_ctor_set(v___x_5299_, 3, v___x_5275_);
lean_ctor_set_usize(v___x_5299_, 4, v___x_5298_);
v___x_5300_ = lean_box(1);
lean_inc_ref(v___x_5299_);
v___x_5301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5294_);
lean_ctor_set(v___x_5301_, 1, v___x_5299_);
lean_ctor_set(v___x_5301_, 2, v___x_5300_);
v___x_5302_ = lean_mk_empty_array_with_capacity(v___x_5275_);
v___x_5303_ = lean_box(0);
lean_inc(v___x_5276_);
v___x_5304_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5304_, 0, v___x_5293_);
lean_ctor_set(v___x_5304_, 1, v___x_5276_);
lean_ctor_set(v___x_5304_, 2, v___x_5301_);
lean_ctor_set(v___x_5304_, 3, v___x_5302_);
lean_ctor_set(v___x_5304_, 4, v___x_5303_);
lean_ctor_set(v___x_5304_, 5, v___x_5275_);
lean_ctor_set(v___x_5304_, 6, v___x_5303_);
lean_ctor_set_uint8(v___x_5304_, sizeof(void*)*7, v___x_5291_);
lean_ctor_set_uint8(v___x_5304_, sizeof(void*)*7 + 1, v___x_5291_);
lean_ctor_set_uint8(v___x_5304_, sizeof(void*)*7 + 2, v___x_5291_);
lean_ctor_set_uint8(v___x_5304_, sizeof(void*)*7 + 3, v___x_5292_);
v___x_5305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5275_);
lean_ctor_set(v___x_5305_, 1, v___x_5275_);
lean_ctor_set(v___x_5305_, 2, v___x_5275_);
lean_ctor_set(v___x_5305_, 3, v___x_5294_);
lean_ctor_set(v___x_5305_, 4, v___x_5294_);
lean_ctor_set(v___x_5305_, 5, v___x_5294_);
lean_ctor_set(v___x_5305_, 6, v___x_5294_);
lean_ctor_set(v___x_5305_, 7, v___x_5294_);
lean_ctor_set(v___x_5305_, 8, v___x_5294_);
v___x_5306_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5307_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5305_);
lean_ctor_set(v___x_5308_, 1, v___x_5306_);
lean_ctor_set(v___x_5308_, 2, v___x_5276_);
lean_ctor_set(v___x_5308_, 3, v___x_5299_);
lean_ctor_set(v___x_5308_, 4, v___x_5307_);
v___x_5309_ = lean_st_mk_ref(v___x_5308_);
v___x_5310_ = l_Lean_Meta_addDefaultInstance(v_declName_5278_, v_a_5287_, v___x_5304_, v___x_5309_, v___y_5289_, v___y_5290_);
lean_dec_ref(v___x_5304_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5319_; 
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5310_, 0);
lean_dec(v_unused_5320_);
v___x_5312_ = v___x_5310_;
v_isShared_5313_ = v_isSharedCheck_5319_;
goto v_resetjp_5311_;
}
else
{
lean_dec(v___x_5310_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5319_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5317_; 
v___x_5314_ = lean_st_ref_get(v___x_5309_);
lean_dec(v___x_5309_);
lean_dec(v___x_5314_);
v___x_5315_ = lean_box(0);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5315_);
v___x_5317_ = v___x_5312_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
else
{
lean_dec(v___x_5309_);
return v___x_5310_;
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec(v_declName_5278_);
lean_dec(v___x_5277_);
lean_dec(v___x_5276_);
lean_dec(v___x_5275_);
v_a_5324_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5286_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5286_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5332_, lean_object* v___x_5333_, lean_object* v___x_5334_, lean_object* v_declName_5335_, lean_object* v_stx_5336_, lean_object* v_kind_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
uint8_t v_kind_boxed_5341_; lean_object* v_res_5342_; 
v_kind_boxed_5341_ = lean_unbox(v_kind_5337_);
v_res_5342_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5332_, v___x_5333_, v___x_5334_, v_declName_5335_, v_stx_5336_, v_kind_boxed_5341_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v_stx_5336_);
return v_res_5342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5345_ = l_Lean_stringToMessageData(v___x_5344_);
return v___x_5345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5348_ = l_Lean_stringToMessageData(v___x_5347_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5349_, lean_object* v_decl_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5354_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5355_ = l_Lean_MessageData_ofName(v___x_5349_);
v___x_5356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5354_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5356_);
lean_ctor_set(v___x_5358_, 1, v___x_5357_);
v___x_5359_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5358_, v___y_5351_, v___y_5352_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5360_, lean_object* v_decl_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5360_, v_decl_5361_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v_decl_5361_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5400_ = l_Lean_registerBuiltinAttribute(v___x_5399_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v___x_5401_; uint8_t v___x_5402_; lean_object* v___x_5403_; 
lean_dec_ref(v___x_5400_);
v___x_5401_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5402_ = 0;
v___x_5403_ = l_Lean_registerTraceClass(v___x_5401_, v___x_5402_, v___x_5398_);
return v___x_5403_;
}
else
{
return v___x_5400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5406_, lean_object* v_name_5407_, uint8_t v_kind_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; 
v___x_5412_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5407_, v_kind_5408_, v___y_5409_, v___y_5410_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5413_, lean_object* v_name_5414_, lean_object* v_kind_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
uint8_t v_kind_boxed_5419_; lean_object* v_res_5420_; 
v_kind_boxed_5419_ = lean_unbox(v_kind_5415_);
v_res_5420_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5413_, v_name_5414_, v_kind_boxed_5419_, v___y_5416_, v___y_5417_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5421_, lean_object* v_toPure_5422_, lean_object* v_____do__lift_5423_){
_start:
{
lean_object* v___x_5424_; lean_object* v_toEnvExtension_5425_; lean_object* v_asyncMode_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v_priorities_5429_; lean_object* v___x_5430_; 
v___x_5424_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5425_ = lean_ctor_get(v___x_5424_, 0);
v_asyncMode_5426_ = lean_ctor_get(v_toEnvExtension_5425_, 2);
v___x_5427_ = lean_box(0);
v___x_5428_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5421_, v___x_5424_, v_____do__lift_5423_, v_asyncMode_5426_, v___x_5427_);
v_priorities_5429_ = lean_ctor_get(v___x_5428_, 1);
lean_inc(v_priorities_5429_);
lean_dec(v___x_5428_);
v___x_5430_ = lean_apply_2(v_toPure_5422_, lean_box(0), v_priorities_5429_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5431_, lean_object* v_inst_5432_){
_start:
{
lean_object* v_toApplicative_5433_; lean_object* v_toBind_5434_; lean_object* v_getEnv_5435_; lean_object* v_toPure_5436_; lean_object* v___x_5437_; lean_object* v___f_5438_; lean_object* v___x_5439_; 
v_toApplicative_5433_ = lean_ctor_get(v_inst_5431_, 0);
lean_inc_ref(v_toApplicative_5433_);
v_toBind_5434_ = lean_ctor_get(v_inst_5431_, 1);
lean_inc(v_toBind_5434_);
lean_dec_ref(v_inst_5431_);
v_getEnv_5435_ = lean_ctor_get(v_inst_5432_, 0);
lean_inc(v_getEnv_5435_);
lean_dec_ref(v_inst_5432_);
v_toPure_5436_ = lean_ctor_get(v_toApplicative_5433_, 1);
lean_inc(v_toPure_5436_);
lean_dec_ref(v_toApplicative_5433_);
v___x_5437_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5438_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5438_, 0, v___x_5437_);
lean_closure_set(v___f_5438_, 1, v_toPure_5436_);
v___x_5439_ = lean_apply_4(v_toBind_5434_, lean_box(0), lean_box(0), v_getEnv_5435_, v___f_5438_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5440_, lean_object* v_inst_5441_, lean_object* v_inst_5442_){
_start:
{
lean_object* v___x_5443_; 
v___x_5443_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5441_, v_inst_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5444_, lean_object* v_className_5445_, lean_object* v_toPure_5446_, lean_object* v_____do__lift_5447_){
_start:
{
lean_object* v___x_5448_; lean_object* v_toEnvExtension_5449_; lean_object* v_asyncMode_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v_defaultInstances_5453_; lean_object* v___x_5454_; 
v___x_5448_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5449_ = lean_ctor_get(v___x_5448_, 0);
v_asyncMode_5450_ = lean_ctor_get(v_toEnvExtension_5449_, 2);
v___x_5451_ = lean_box(0);
v___x_5452_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5444_, v___x_5448_, v_____do__lift_5447_, v_asyncMode_5450_, v___x_5451_);
v_defaultInstances_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc(v_defaultInstances_5453_);
lean_dec(v___x_5452_);
v___x_5454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5453_, v_className_5445_);
lean_dec(v_defaultInstances_5453_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5455_ = lean_box(0);
v___x_5456_ = lean_apply_2(v_toPure_5446_, lean_box(0), v___x_5455_);
return v___x_5456_;
}
else
{
lean_object* v_val_5457_; lean_object* v___x_5458_; 
v_val_5457_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_val_5457_);
lean_dec_ref(v___x_5454_);
v___x_5458_ = lean_apply_2(v_toPure_5446_, lean_box(0), v_val_5457_);
return v___x_5458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5459_, lean_object* v_className_5460_, lean_object* v_toPure_5461_, lean_object* v_____do__lift_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5459_, v_className_5460_, v_toPure_5461_, v_____do__lift_5462_);
lean_dec(v_className_5460_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5464_, lean_object* v_inst_5465_, lean_object* v_className_5466_){
_start:
{
lean_object* v_toApplicative_5467_; lean_object* v_toBind_5468_; lean_object* v_getEnv_5469_; lean_object* v_toPure_5470_; lean_object* v___x_5471_; lean_object* v___f_5472_; lean_object* v___x_5473_; 
v_toApplicative_5467_ = lean_ctor_get(v_inst_5464_, 0);
lean_inc_ref(v_toApplicative_5467_);
v_toBind_5468_ = lean_ctor_get(v_inst_5464_, 1);
lean_inc(v_toBind_5468_);
lean_dec_ref(v_inst_5464_);
v_getEnv_5469_ = lean_ctor_get(v_inst_5465_, 0);
lean_inc(v_getEnv_5469_);
lean_dec_ref(v_inst_5465_);
v_toPure_5470_ = lean_ctor_get(v_toApplicative_5467_, 1);
lean_inc(v_toPure_5470_);
lean_dec_ref(v_toApplicative_5467_);
v___x_5471_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5472_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5472_, 0, v___x_5471_);
lean_closure_set(v___f_5472_, 1, v_className_5466_);
lean_closure_set(v___f_5472_, 2, v_toPure_5470_);
v___x_5473_ = lean_apply_4(v_toBind_5468_, lean_box(0), lean_box(0), v_getEnv_5469_, v___f_5472_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5474_, lean_object* v_inst_5475_, lean_object* v_inst_5476_, lean_object* v_className_5477_){
_start:
{
lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5475_, v_inst_5476_, v_className_5477_);
return v___x_5478_;
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
