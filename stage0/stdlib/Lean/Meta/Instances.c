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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "synthOrder"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 119, 89, 231, 199, 121, 219, 201)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "synthesizing the arguments of "};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " in the order "};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "instance does not provide concrete values for (semi-)out-params"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9;
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
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
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
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0));
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
return v___x_332_;
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
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__1);
lean_inc(v_k_426_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_k_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
lean_inc(v_k_426_);
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
v___x_542_ = lean_panic_fn(v___x_541_, v_msg_540_);
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
lean_inc(v_val_813_);
lean_dec_ref(v___x_809_);
lean_inc(v_val_813_);
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
lean_inc(v_declName_1073_);
lean_inc_ref(v_d_1072_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1080_, 0, v_d_1072_);
lean_closure_set(v___f_1080_, 1, v_declName_1073_);
lean_closure_set(v___f_1080_, 2, v_toPure_1076_);
lean_inc(v_declName_1073_);
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
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1202_, lean_object* v___x_1203_, uint8_t v___x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
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
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
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
uint8_t v___x_532__boxed_1232_; lean_object* v_res_1233_; 
v___x_532__boxed_1232_ = lean_unbox(v___x_1226_);
v_res_1233_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1224_, v___x_1225_, v___x_532__boxed_1232_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
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
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
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
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1263_, lean_object* v_b_1264_, lean_object* v_c_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_apply_7(v_k_1263_, v_b_1264_, v_c_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1272_, lean_object* v_b_1273_, lean_object* v_c_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1272_, v_b_1273_, v_c_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
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
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
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
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
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
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
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
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
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
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
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
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
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
size_t v_x_1636__boxed_1646_; size_t v_x_1637__boxed_1647_; lean_object* v_res_1648_; 
v_x_1636__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_x_1637__boxed_1647_ = lean_unbox_usize(v_x_1643_);
lean_dec(v_x_1643_);
v_res_1648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1641_, v_x_1636__boxed_1646_, v_x_1637__boxed_1647_, v_x_1644_, v_x_1645_);
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
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
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
lean_inc(v___y_1715_);
lean_inc_ref(v___y_1714_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
v___y_1722_ = v___y_1712_;
v___y_1723_ = v___y_1713_;
v___y_1724_ = v___y_1714_;
v___y_1725_ = v___y_1715_;
goto v___jp_1721_;
}
else
{
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v___x_1747_;
}
}
else
{
lean_dec(v___x_1743_);
lean_inc(v___y_1715_);
lean_inc_ref(v___y_1714_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
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
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v___x_1729_;
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
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
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
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
size_t v_x_2020__boxed_1835_; size_t v_x_2021__boxed_1836_; lean_object* v_res_1837_; 
v_x_2020__boxed_1835_ = lean_unbox_usize(v_x_1831_);
lean_dec(v_x_1831_);
v_x_2021__boxed_1836_ = lean_unbox_usize(v_x_1832_);
lean_dec(v_x_1832_);
v_res_1837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(v_00_u03b2_1829_, v_x_1830_, v_x_2020__boxed_1835_, v_x_2021__boxed_1836_, v_x_1833_, v_x_1834_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg(lean_object* v_cls_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_options_1929_; uint8_t v_hasTrace_1930_; 
v_options_1929_ = lean_ctor_get(v___y_1927_, 2);
v_hasTrace_1930_ = lean_ctor_get_uint8(v_options_1929_, sizeof(void*)*1);
if (v_hasTrace_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v_cls_1926_);
v___x_1931_ = lean_box(v_hasTrace_1930_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v_inheritedTraceOptions_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_inheritedTraceOptions_1933_ = lean_ctor_get(v___y_1927_, 13);
v___x_1934_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__1));
v___x_1935_ = l_Lean_Name_append(v___x_1934_, v_cls_1926_);
v___x_1936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1933_, v_options_1929_, v___x_1935_);
lean_dec(v___x_1935_);
v___x_1937_ = lean_box(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___boxed(lean_object* v_cls_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg(v_cls_1939_, v___y_1940_);
lean_dec_ref(v___y_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_cls_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg(v_cls_1943_, v___y_1946_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_cls_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_cls_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1957_, lean_object* v_as_1958_, size_t v_i_1959_, size_t v_stop_1960_){
_start:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_usize_dec_eq(v_i_1959_, v_stop_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_array_uget_borrowed(v_as_1958_, v_i_1959_);
v___x_1963_ = lean_nat_dec_eq(v_a_1957_, v___x_1962_);
if (v___x_1963_ == 0)
{
size_t v___x_1964_; size_t v___x_1965_; 
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1959_, v___x_1964_);
v_i_1959_ = v___x_1965_;
goto _start;
}
else
{
return v___x_1963_;
}
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = 0;
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1968_, lean_object* v_as_1969_, lean_object* v_i_1970_, lean_object* v_stop_1971_){
_start:
{
size_t v_i_boxed_1972_; size_t v_stop_boxed_1973_; uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_i_boxed_1972_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_stop_boxed_1973_ = lean_unbox_usize(v_stop_1971_);
lean_dec(v_stop_1971_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1968_, v_as_1969_, v_i_boxed_1972_, v_stop_boxed_1973_);
lean_dec_ref(v_as_1969_);
lean_dec(v_a_1968_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = lean_array_get_size(v_as_1976_);
v___x_1980_ = lean_nat_dec_lt(v___x_1978_, v___x_1979_);
if (v___x_1980_ == 0)
{
return v___x_1980_;
}
else
{
if (v___x_1980_ == 0)
{
return v___x_1980_;
}
else
{
size_t v___x_1981_; size_t v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = lean_usize_of_nat(v___x_1979_);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1977_, v_as_1976_, v___x_1981_, v___x_1982_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1984_, lean_object* v_a_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_as_1984_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1988_, lean_object* v_fst_1989_, lean_object* v_argVars_1990_, lean_object* v_as_1991_, size_t v_sz_1992_, size_t v_i_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_a_2001_; uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1993_, v_sz_1992_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1994_);
return v___x_2006_;
}
else
{
lean_object* v_next_2007_; 
v_next_2007_ = lean_ctor_get(v_b_1994_, 0);
lean_inc(v_next_2007_);
if (lean_obj_tag(v_next_2007_) == 0)
{
lean_object* v___x_2008_; 
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1994_);
return v___x_2008_;
}
else
{
lean_object* v_upperBound_2009_; lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2041_; 
v_upperBound_2009_ = lean_ctor_get(v_b_1994_, 1);
v_val_2010_ = lean_ctor_get(v_next_2007_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_next_2007_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2012_ = v_next_2007_;
v_isShared_2013_ = v_isSharedCheck_2041_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_dec(v_next_2007_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2041_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_nat_dec_lt(v_val_2010_, v_upperBound_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_del_object(v___x_2012_);
lean_dec(v_val_2010_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_1994_);
return v___x_2015_;
}
else
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2038_; 
lean_inc(v_upperBound_2009_);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_b_1994_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2039_ = lean_ctor_get(v_b_1994_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_b_1994_, 0);
lean_dec(v_unused_2040_);
v___x_2017_ = v_b_1994_;
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_b_1994_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_val_2010_, v___x_2019_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2020_);
v___x_2022_ = v___x_2012_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2022_);
v___x_2024_ = v___x_2017_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_upperBound_2009_);
v___x_2024_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1988_, v_val_2010_);
lean_dec(v_val_2010_);
if (v___x_2025_ == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_1991_, v_i_1993_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v_a_2026_);
v___x_2027_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1989_, v_argVars_1990_, v_a_2026_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref(v___x_2027_);
v_a_2001_ = v___x_2024_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v___x_2024_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
v_a_2001_ = v___x_2024_;
goto v___jp_2000_;
}
}
}
}
}
}
}
}
v___jp_2000_:
{
size_t v___x_2002_; size_t v___x_2003_; 
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1993_, v___x_2002_);
v_i_1993_ = v___x_2003_;
v_b_1994_ = v_a_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2042_, lean_object* v_fst_2043_, lean_object* v_argVars_2044_, lean_object* v_as_2045_, lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
size_t v_sz_boxed_2054_; size_t v_i_boxed_2055_; lean_object* v_res_2056_; 
v_sz_boxed_2054_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2055_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2042_, v_fst_2043_, v_argVars_2044_, v_as_2045_, v_sz_boxed_2054_, v_i_boxed_2055_, v_b_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec_ref(v_as_2045_);
lean_dec_ref(v_argVars_2044_);
lean_dec_ref(v_fst_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
if (lean_obj_tag(v_a_2058_) == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = l_List_reverse___redArg(v_a_2059_);
return v___x_2060_;
}
else
{
lean_object* v_head_2061_; lean_object* v_tail_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2077_; 
v_head_2061_ = lean_ctor_get(v_a_2058_, 0);
v_tail_2062_ = lean_ctor_get(v_a_2058_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2058_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2064_ = v_a_2058_;
v_isShared_2065_ = v_isSharedCheck_2077_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_tail_2062_);
lean_inc(v_head_2061_);
lean_dec(v_a_2058_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2077_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; uint8_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2066_ = 0;
v___x_2067_ = lean_box(v___x_2066_);
v___x_2068_ = lean_array_get_borrowed(v___x_2067_, v_fst_2057_, v_head_2061_);
v___x_2069_ = 3;
v___x_2070_ = lean_unbox(v___x_2068_);
v___x_2071_ = l_Lean_instBEqBinderInfo_beq(v___x_2070_, v___x_2069_);
if (v___x_2071_ == 0)
{
lean_del_object(v___x_2064_);
lean_dec(v_head_2061_);
v_a_2058_ = v_tail_2062_;
goto _start;
}
else
{
lean_object* v___x_2074_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v_a_2059_);
v___x_2074_ = v___x_2064_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_head_2061_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_a_2059_);
v___x_2074_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v_a_2058_ = v_tail_2062_;
v_a_2059_ = v___x_2074_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2078_, v_a_2079_, v_a_2080_);
lean_dec_ref(v_fst_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2082_, lean_object* v___x_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_b_2086_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_nat_dec_lt(v_a_2085_, v_upperBound_2082_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_a_2085_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_b_2086_);
return v___x_2089_;
}
else
{
lean_object* v_snd_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2131_; 
v_snd_2090_ = lean_ctor_get(v_b_2086_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_b_2086_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v_b_2086_, 0);
lean_dec(v_unused_2132_);
v___x_2092_ = v_b_2086_;
v_isShared_2093_ = v_isSharedCheck_2131_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snd_2090_);
lean_dec(v_b_2086_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2131_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_array_2094_; lean_object* v_start_2095_; lean_object* v_stop_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_array_2094_ = lean_ctor_get(v_snd_2090_, 0);
v_start_2095_ = lean_ctor_get(v_snd_2090_, 1);
v_stop_2096_ = lean_ctor_get(v_snd_2090_, 2);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_nat_dec_lt(v_start_2095_, v_stop_2096_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v_a_2085_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2097_);
v___x_2100_ = v___x_2092_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_snd_2090_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
else
{
lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2127_; 
lean_inc(v_stop_2096_);
lean_inc(v_start_2095_);
lean_inc_ref(v_array_2094_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_snd_2090_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; 
v_unused_2128_ = lean_ctor_get(v_snd_2090_, 2);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_snd_2090_, 1);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_snd_2090_, 0);
lean_dec(v_unused_2130_);
v___x_2104_ = v_snd_2090_;
v_isShared_2105_ = v_isSharedCheck_2127_;
goto v_resetjp_2103_;
}
else
{
lean_dec(v_snd_2090_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2127_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_nat_dec_eq(v___x_2083_, v___x_2106_);
v___x_2108_ = lean_array_fget(v_array_2094_, v_start_2095_);
v___x_2109_ = lean_unsigned_to_nat(1u);
v___x_2110_ = lean_nat_add(v_start_2095_, v___x_2109_);
lean_dec(v_start_2095_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2110_);
v___x_2112_ = v___x_2104_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_array_2094_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_stop_2096_);
v___x_2112_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
uint8_t v___x_2125_; 
v___x_2125_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2084_, v_a_2085_);
if (v___x_2125_ == 0)
{
goto v___jp_2119_;
}
else
{
if (v___x_2107_ == 0)
{
lean_dec(v___x_2108_);
goto v___jp_2113_;
}
else
{
goto v___jp_2119_;
}
}
v___jp_2113_:
{
lean_object* v___x_2115_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2112_);
lean_ctor_set(v___x_2092_, 0, v___x_2097_);
v___x_2115_ = v___x_2092_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2112_);
v___x_2115_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_nat_add(v_a_2085_, v___x_2109_);
lean_dec(v_a_2085_);
v_a_2085_ = v___x_2116_;
v_b_2086_ = v___x_2115_;
goto _start;
}
}
v___jp_2119_:
{
uint8_t v___x_2120_; 
v___x_2120_ = l_Lean_Expr_hasExprMVar(v___x_2108_);
lean_dec(v___x_2108_);
if (v___x_2120_ == 0)
{
goto v___jp_2113_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2092_);
lean_dec(v_a_2085_);
v___x_2121_ = lean_box(v___x_2107_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2112_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2133_, lean_object* v___x_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2133_, v___x_2134_, v_a_2135_, v_a_2136_, v_b_2137_);
lean_dec_ref(v_a_2135_);
lean_dec(v___x_2134_);
lean_dec(v_upperBound_2133_);
return v_res_2139_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2140_; lean_object* v_dummy_2141_; 
v___x_2140_ = lean_box(0);
v_dummy_2141_ = l_Lean_Expr_sort___override(v___x_2140_);
return v_dummy_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2142_, lean_object* v___x_2143_, uint8_t v___x_2144_, lean_object* v_x_2145_, lean_object* v_argTy_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
v___x_2152_ = lean_whnf(v_argTy_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2153_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_dummy_2156_; lean_object* v_nargs_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v_dummy_2156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2157_ = l_Lean_Expr_getAppNumArgs(v_a_2153_);
lean_inc(v_nargs_2157_);
v___x_2158_ = lean_mk_array(v_nargs_2157_, v_dummy_2156_);
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_sub(v_nargs_2157_, v___x_2159_);
lean_dec(v_nargs_2157_);
v___x_2161_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2153_, v___x_2158_, v___x_2160_);
v___x_2162_ = lean_array_get_size(v___x_2161_);
lean_inc(v___x_2142_);
v___x_2163_ = l_Array_toSubarray___redArg(v___x_2161_, v___x_2142_, v___x_2162_);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___x_2163_);
v___x_2166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2162_, v___x_2143_, v_a_2155_, v___x_2142_, v___x_2165_);
lean_dec(v_a_2155_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2180_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2180_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_fst_2171_; 
v_fst_2171_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_fst_2171_);
lean_dec(v_a_2167_);
if (lean_obj_tag(v_fst_2171_) == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(v___x_2144_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2172_);
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
else
{
lean_object* v_val_2176_; lean_object* v___x_2178_; 
v_val_2176_ = lean_ctor_get(v_fst_2171_, 0);
lean_inc(v_val_2176_);
lean_dec_ref(v_fst_2171_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v_val_2176_);
v___x_2178_ = v___x_2169_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_val_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2166_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2166_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2153_);
lean_dec(v___x_2142_);
v_a_2189_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2154_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2154_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___x_2142_);
v_a_2197_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2152_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2152_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v_x_2208_, lean_object* v_argTy_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
uint8_t v___x_24656__boxed_2215_; lean_object* v_res_2216_; 
v___x_24656__boxed_2215_ = lean_unbox(v___x_2207_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2205_, v___x_2206_, v___x_24656__boxed_2215_, v_x_2208_, v_argTy_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec_ref(v_x_2208_);
lean_dec(v___x_2206_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2220_, lean_object* v_projInfo_x3f_2221_, lean_object* v___x_2222_, lean_object* v_argVars_2223_, lean_object* v_as_2224_, size_t v_sz_2225_, size_t v_i_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_lt(v_i_2226_, v_sz_2225_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; 
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___x_2222_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v_b_2227_);
return v___x_2234_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref(v_b_2227_);
v_a_2235_ = lean_array_uget_borrowed(v_as_2224_, v_i_2226_);
v___x_2236_ = l_Lean_instInhabitedExpr;
v___x_2237_ = lean_array_get_borrowed(v___x_2236_, v_fst_2220_, v_a_2235_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___x_2237_);
v___x_2238_ = lean_infer_type(v___x_2237_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2239_, v___y_2229_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2287_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2287_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2287_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2253_; lean_object* v___y_2255_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___f_2271_; uint8_t v___x_2272_; 
v___x_2245_ = lean_box(0);
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_box(v___x_2233_);
lean_inc(v___x_2222_);
v___f_2271_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2271_, 0, v___x_2269_);
lean_closure_set(v___f_2271_, 1, v___x_2222_);
lean_closure_set(v___f_2271_, 2, v___x_2270_);
v___x_2272_ = lean_nat_dec_eq(v___x_2222_, v___x_2269_);
if (lean_obj_tag(v_projInfo_x3f_2221_) == 1)
{
lean_object* v_val_2273_; lean_object* v_numParams_2274_; uint8_t v___x_2275_; 
v_val_2273_ = lean_ctor_get(v_projInfo_x3f_2221_, 0);
v_numParams_2274_ = lean_ctor_get(v_val_2273_, 1);
v___x_2275_ = lean_nat_dec_eq(v_numParams_2274_, v_a_2235_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
v___x_2276_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2241_, v___f_2271_, v___x_2272_, v___x_2272_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
v___y_2255_ = v___x_2276_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2277_; 
lean_dec_ref(v___f_2271_);
lean_dec(v___x_2222_);
v___x_2277_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2220_, v_argVars_2223_, v_a_2241_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref(v___x_2277_);
goto v___jp_2246_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_del_object(v___x_2243_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v___x_2286_; 
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
v___x_2286_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2241_, v___f_2271_, v___x_2272_, v___x_2272_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
v___y_2255_ = v___x_2286_;
goto v___jp_2254_;
}
v___jp_2246_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_inc(v_a_2235_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2235_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2245_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2249_);
v___x_2251_ = v___x_2243_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
v___jp_2254_:
{
if (lean_obj_tag(v___y_2255_) == 0)
{
lean_object* v_a_2256_; uint8_t v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___y_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___y_2255_);
v___x_2257_ = lean_unbox(v_a_2256_);
lean_dec(v_a_2256_);
if (v___x_2257_ == 0)
{
size_t v___x_2258_; size_t v___x_2259_; 
lean_del_object(v___x_2243_);
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2226_, v___x_2258_);
v_i_2226_ = v___x_2259_;
v_b_2227_ = v___x_2253_;
goto _start;
}
else
{
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___x_2222_);
goto v___jp_2246_;
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_del_object(v___x_2243_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___x_2222_);
v_a_2261_ = lean_ctor_get(v___y_2255_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2255_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___y_2255_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___y_2255_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___x_2222_);
v_a_2288_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2240_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2240_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___x_2222_);
v_a_2296_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2238_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2238_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2304_, lean_object* v_projInfo_x3f_2305_, lean_object* v___x_2306_, lean_object* v_argVars_2307_, lean_object* v_as_2308_, lean_object* v_sz_2309_, lean_object* v_i_2310_, lean_object* v_b_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
size_t v_sz_boxed_2317_; size_t v_i_boxed_2318_; lean_object* v_res_2319_; 
v_sz_boxed_2317_ = lean_unbox_usize(v_sz_2309_);
lean_dec(v_sz_2309_);
v_i_boxed_2318_ = lean_unbox_usize(v_i_2310_);
lean_dec(v_i_2310_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2304_, v_projInfo_x3f_2305_, v___x_2306_, v_argVars_2307_, v_as_2308_, v_sz_boxed_2317_, v_i_boxed_2318_, v_b_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec_ref(v_as_2308_);
lean_dec_ref(v_argVars_2307_);
lean_dec(v_projInfo_x3f_2305_);
lean_dec_ref(v_fst_2304_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v_env_2327_; lean_object* v___x_2328_; lean_object* v_mctx_2329_; lean_object* v_lctx_2330_; lean_object* v_options_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2326_ = lean_st_ref_get(v___y_2324_);
v_env_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_ref(v_env_2327_);
lean_dec(v___x_2326_);
v___x_2328_ = lean_st_ref_get(v___y_2322_);
v_mctx_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_mctx_2329_);
lean_dec(v___x_2328_);
v_lctx_2330_ = lean_ctor_get(v___y_2321_, 2);
v_options_2331_ = lean_ctor_get(v___y_2323_, 2);
lean_inc_ref(v_options_2331_);
lean_inc_ref(v_lctx_2330_);
v___x_2332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2332_, 0, v_env_2327_);
lean_ctor_set(v___x_2332_, 1, v_mctx_2329_);
lean_ctor_set(v___x_2332_, 2, v_lctx_2330_);
lean_ctor_set(v___x_2332_, 3, v_options_2331_);
v___x_2333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v_msgData_2320_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_ref_2348_; lean_object* v___x_2349_; lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2358_; 
v_ref_2348_ = lean_ctor_get(v___y_2345_, 5);
v___x_2349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_ref_2348_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_ref_2348_);
lean_ctor_set(v___x_2354_, 1, v_a_2350_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2366_, lean_object* v_as_2367_, size_t v_i_2368_, size_t v_stop_2369_, lean_object* v_b_2370_){
_start:
{
lean_object* v___y_2372_; uint8_t v___x_2376_; 
v___x_2376_ = lean_usize_dec_eq(v_i_2368_, v_stop_2369_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = lean_array_uget_borrowed(v_as_2367_, v_i_2368_);
v___x_2378_ = lean_nat_dec_eq(v___x_2377_, v_next_2366_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_inc(v___x_2377_);
v___x_2379_ = lean_array_push(v_b_2370_, v___x_2377_);
v___y_2372_ = v___x_2379_;
goto v___jp_2371_;
}
else
{
v___y_2372_ = v_b_2370_;
goto v___jp_2371_;
}
}
else
{
return v_b_2370_;
}
v___jp_2371_:
{
size_t v___x_2373_; size_t v___x_2374_; 
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_add(v_i_2368_, v___x_2373_);
v_i_2368_ = v___x_2374_;
v_b_2370_ = v___y_2372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2380_, lean_object* v_as_2381_, lean_object* v_i_2382_, lean_object* v_stop_2383_, lean_object* v_b_2384_){
_start:
{
size_t v_i_boxed_2385_; size_t v_stop_boxed_2386_; lean_object* v_res_2387_; 
v_i_boxed_2385_ = lean_unbox_usize(v_i_2382_);
lean_dec(v_i_2382_);
v_stop_boxed_2386_ = lean_unbox_usize(v_stop_2383_);
lean_dec(v_stop_2383_);
v_res_2387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2380_, v_as_2381_, v_i_boxed_2385_, v_stop_boxed_2386_, v_b_2384_);
lean_dec_ref(v_as_2381_);
lean_dec(v_next_2380_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2388_, size_t v_sz_2389_, size_t v_i_2390_, lean_object* v_bs_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_usize_dec_lt(v_i_2390_, v_sz_2389_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_bs_2391_);
return v___x_2398_;
}
else
{
lean_object* v_v_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_v_2399_ = lean_array_uget_borrowed(v_bs_2391_, v_i_2390_);
v___x_2400_ = l_Lean_instInhabitedExpr;
v___x_2401_ = lean_array_get_borrowed(v___x_2400_, v_fst_2388_, v_v_2399_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc(v___x_2401_);
v___x_2402_ = lean_infer_type(v___x_2401_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2403_, v___y_2393_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v_bs_x27_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = lean_unsigned_to_nat(0u);
v_bs_x27_2407_ = lean_array_uset(v_bs_2391_, v_i_2390_, v___x_2406_);
v___x_2408_ = l_Lean_Expr_setPPExplicit(v_a_2405_, v___x_2397_);
v___x_2409_ = l_Lean_indentExpr(v___x_2408_);
v___x_2410_ = ((size_t)1ULL);
v___x_2411_ = lean_usize_add(v_i_2390_, v___x_2410_);
v___x_2412_ = lean_array_uset(v_bs_x27_2407_, v_i_2390_, v___x_2409_);
v_i_2390_ = v___x_2411_;
v_bs_2391_ = v___x_2412_;
goto _start;
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_bs_2391_);
v_a_2414_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2404_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2404_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_bs_2391_);
v_a_2422_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2402_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2402_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2430_, lean_object* v_sz_2431_, lean_object* v_i_2432_, lean_object* v_bs_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
size_t v_sz_boxed_2439_; size_t v_i_boxed_2440_; lean_object* v_res_2441_; 
v_sz_boxed_2439_ = lean_unbox_usize(v_sz_2431_);
lean_dec(v_sz_2431_);
v_i_boxed_2440_ = lean_unbox_usize(v_i_2432_);
lean_dec(v_i_2432_);
v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2430_, v_sz_boxed_2439_, v_i_boxed_2440_, v_bs_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec_ref(v_fst_2430_);
return v_res_2441_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2446_ = l_Lean_MessageData_ofFormat(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2456_, lean_object* v_argVars_2457_, lean_object* v_inst_2458_, lean_object* v_a_2459_, lean_object* v_projInfo_x3f_2460_, lean_object* v_b_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2598_; 
v_fst_2507_ = lean_ctor_get(v_b_2461_, 0);
v_snd_2508_ = lean_ctor_get(v_b_2461_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_b_2461_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2510_ = v_b_2461_;
v_isShared_2511_ = v_isSharedCheck_2598_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_snd_2508_);
lean_inc(v_fst_2507_);
lean_dec(v_b_2461_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2598_;
goto v_resetjp_2509_;
}
v___jp_2467_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = l_Lean_instInhabitedExpr;
v___x_2476_ = lean_array_get_borrowed(v___x_2475_, v_fst_2456_, v___y_2469_);
lean_dec(v___y_2469_);
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2471_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2468_);
lean_inc(v___x_2476_);
v___x_2477_ = lean_infer_type(v___x_2476_, v___y_2468_, v___y_2470_, v___y_2471_, v___y_2473_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2471_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2468_);
v___x_2479_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2456_, v_argVars_2457_, v_a_2478_, v___y_2468_, v___y_2470_, v___y_2471_, v___y_2473_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v___x_2480_; 
lean_dec_ref(v___x_2479_);
lean_inc(v___x_2476_);
v___x_2480_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2456_, v_argVars_2457_, v___x_2476_, v___y_2468_, v___y_2470_, v___y_2471_, v___y_2473_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2481_; 
lean_dec_ref(v___x_2480_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___y_2472_);
lean_ctor_set(v___x_2481_, 1, v___y_2474_);
v_b_2461_ = v___x_2481_;
goto _start;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2483_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2480_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2491_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2479_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2479_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2499_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2477_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2477_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
v_resetjp_2509_:
{
lean_object* v_next_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_array_get_size(v_snd_2508_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_nat_dec_eq(v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; size_t v_sz_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2510_);
v___x_2578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2579_ = lean_array_size(v_snd_2508_);
v___x_2580_ = ((size_t)0ULL);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2456_, v_projInfo_x3f_2460_, v___x_2575_, v_argVars_2457_, v_snd_2508_, v_sz_2579_, v___x_2580_, v___x_2578_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_fst_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
v_fst_2583_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_fst_2583_);
lean_dec(v_a_2582_);
if (lean_obj_tag(v_fst_2583_) == 0)
{
goto v___jp_2537_;
}
else
{
lean_object* v_val_2584_; 
v_val_2584_ = lean_ctor_get(v_fst_2583_, 0);
lean_inc(v_val_2584_);
lean_dec_ref(v_fst_2583_);
if (lean_obj_tag(v_val_2584_) == 0)
{
goto v___jp_2537_;
}
else
{
lean_object* v_val_2585_; 
v_val_2585_ = lean_ctor_get(v_val_2584_, 0);
lean_inc(v_val_2585_);
lean_dec_ref(v_val_2584_);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
v_next_2513_ = v_val_2585_;
v___y_2514_ = v___y_2462_;
v___y_2515_ = v___y_2463_;
v___y_2516_ = v___y_2464_;
v___y_2517_ = v___y_2465_;
goto v___jp_2512_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_snd_2508_);
lean_dec(v_fst_2507_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2586_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2581_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2581_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v___x_2595_; 
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
if (v_isShared_2511_ == 0)
{
v___x_2595_ = v___x_2510_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2507_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_snd_2508_);
v___x_2595_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
v___jp_2512_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
lean_inc(v_next_2513_);
v___x_2518_ = lean_array_push(v_fst_2507_, v_next_2513_);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_array_get_size(v_snd_2508_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2522_ = lean_nat_dec_lt(v___x_2519_, v___x_2520_);
if (v___x_2522_ == 0)
{
lean_dec(v_snd_2508_);
v___y_2468_ = v___y_2514_;
v___y_2469_ = v_next_2513_;
v___y_2470_ = v___y_2515_;
v___y_2471_ = v___y_2516_;
v___y_2472_ = v___x_2518_;
v___y_2473_ = v___y_2517_;
v___y_2474_ = v___x_2521_;
goto v___jp_2467_;
}
else
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_nat_dec_le(v___x_2520_, v___x_2520_);
if (v___x_2523_ == 0)
{
if (v___x_2522_ == 0)
{
lean_dec(v_snd_2508_);
v___y_2468_ = v___y_2514_;
v___y_2469_ = v_next_2513_;
v___y_2470_ = v___y_2515_;
v___y_2471_ = v___y_2516_;
v___y_2472_ = v___x_2518_;
v___y_2473_ = v___y_2517_;
v___y_2474_ = v___x_2521_;
goto v___jp_2467_;
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2520_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2513_, v_snd_2508_, v___x_2524_, v___x_2525_, v___x_2521_);
lean_dec(v_snd_2508_);
v___y_2468_ = v___y_2514_;
v___y_2469_ = v_next_2513_;
v___y_2470_ = v___y_2515_;
v___y_2471_ = v___y_2516_;
v___y_2472_ = v___x_2518_;
v___y_2473_ = v___y_2517_;
v___y_2474_ = v___x_2526_;
goto v___jp_2467_;
}
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2520_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2513_, v_snd_2508_, v___x_2527_, v___x_2528_, v___x_2521_);
lean_dec(v_snd_2508_);
v___y_2468_ = v___y_2514_;
v___y_2469_ = v_next_2513_;
v___y_2470_ = v___y_2515_;
v___y_2471_ = v___y_2516_;
v___y_2472_ = v___x_2518_;
v___y_2473_ = v___y_2517_;
v___y_2474_ = v___x_2529_;
goto v___jp_2467_;
}
}
}
v___jp_2530_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = lean_array_get_borrowed(v___x_2535_, v_snd_2508_, v___x_2535_);
lean_inc(v___x_2536_);
v_next_2513_ = v___x_2536_;
v___y_2514_ = v___y_2531_;
v___y_2515_ = v___y_2532_;
v___y_2516_ = v___y_2533_;
v___y_2517_ = v___y_2534_;
goto v___jp_2512_;
}
v___jp_2537_:
{
lean_object* v_options_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_options_2538_ = lean_ctor_get(v___y_2464_, 2);
v___x_2539_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2540_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
v___y_2531_ = v___y_2462_;
v___y_2532_ = v___y_2463_;
v___y_2533_ = v___y_2464_;
v___y_2534_ = v___y_2465_;
goto v___jp_2530_;
}
else
{
size_t v_sz_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v_sz_2541_ = lean_array_size(v_snd_2508_);
v___x_2542_ = ((size_t)0ULL);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
lean_inc(v_snd_2508_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2456_, v_sz_2541_, v___x_2542_, v_snd_2508_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = lean_array_to_list(v_a_2544_);
v___x_2546_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2547_ = l_Lean_MessageData_joinSep(v___x_2545_, v___x_2546_);
v___x_2548_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2458_);
v___x_2549_ = l_Lean_MessageData_ofExpr(v_inst_2458_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_inc_ref(v_a_2459_);
v___x_2553_ = l_Lean_indentExpr(v_a_2459_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2547_);
v___x_2558_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2557_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref(v___x_2558_);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
v___y_2531_ = v___y_2462_;
v___y_2532_ = v___y_2463_;
v___y_2533_ = v___y_2464_;
v___y_2534_ = v___y_2465_;
goto v___jp_2530_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_snd_2508_);
lean_dec(v_fst_2507_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_snd_2508_);
lean_dec(v_fst_2507_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_inst_2458_);
v_a_2567_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2543_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2543_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2599_, lean_object* v_argVars_2600_, lean_object* v_inst_2601_, lean_object* v_a_2602_, lean_object* v_projInfo_x3f_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2599_, v_argVars_2600_, v_inst_2601_, v_a_2602_, v_projInfo_x3f_2603_, v_b_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v_projInfo_x3f_2603_);
lean_dec_ref(v_argVars_2600_);
lean_dec_ref(v_fst_2599_);
return v_res_2610_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2611_; double v___x_2612_; 
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_float_of_nat(v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14(lean_object* v_cls_2615_, lean_object* v_msg_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_ref_2622_; lean_object* v___x_2623_; lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2668_; 
v_ref_2622_ = lean_ctor_get(v___y_2619_, 5);
v___x_2623_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2668_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2668_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v_traceState_2629_; lean_object* v_env_2630_; lean_object* v_nextMacroScope_2631_; lean_object* v_ngen_2632_; lean_object* v_auxDeclNGen_2633_; lean_object* v_cache_2634_; lean_object* v_messages_2635_; lean_object* v_infoState_2636_; lean_object* v_snapshotTasks_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2667_; 
v___x_2628_ = lean_st_ref_take(v___y_2620_);
v_traceState_2629_ = lean_ctor_get(v___x_2628_, 4);
v_env_2630_ = lean_ctor_get(v___x_2628_, 0);
v_nextMacroScope_2631_ = lean_ctor_get(v___x_2628_, 1);
v_ngen_2632_ = lean_ctor_get(v___x_2628_, 2);
v_auxDeclNGen_2633_ = lean_ctor_get(v___x_2628_, 3);
v_cache_2634_ = lean_ctor_get(v___x_2628_, 5);
v_messages_2635_ = lean_ctor_get(v___x_2628_, 6);
v_infoState_2636_ = lean_ctor_get(v___x_2628_, 7);
v_snapshotTasks_2637_ = lean_ctor_get(v___x_2628_, 8);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2639_ = v___x_2628_;
v_isShared_2640_ = v_isSharedCheck_2667_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_snapshotTasks_2637_);
lean_inc(v_infoState_2636_);
lean_inc(v_messages_2635_);
lean_inc(v_cache_2634_);
lean_inc(v_traceState_2629_);
lean_inc(v_auxDeclNGen_2633_);
lean_inc(v_ngen_2632_);
lean_inc(v_nextMacroScope_2631_);
lean_inc(v_env_2630_);
lean_dec(v___x_2628_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2667_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
uint64_t v_tid_2641_; lean_object* v_traces_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2666_; 
v_tid_2641_ = lean_ctor_get_uint64(v_traceState_2629_, sizeof(void*)*1);
v_traces_2642_ = lean_ctor_get(v_traceState_2629_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_traceState_2629_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2644_ = v_traceState_2629_;
v_isShared_2645_ = v_isSharedCheck_2666_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_traces_2642_);
lean_dec(v_traceState_2629_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2666_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; double v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2646_ = lean_box(0);
v___x_2647_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__0);
v___x_2648_ = 0;
v___x_2649_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2650_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2650_, 0, v_cls_2615_);
lean_ctor_set(v___x_2650_, 1, v___x_2646_);
lean_ctor_set(v___x_2650_, 2, v___x_2649_);
lean_ctor_set_float(v___x_2650_, sizeof(void*)*3, v___x_2647_);
lean_ctor_set_float(v___x_2650_, sizeof(void*)*3 + 8, v___x_2647_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*3 + 16, v___x_2648_);
v___x_2651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___closed__1));
v___x_2652_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v_a_2624_);
lean_ctor_set(v___x_2652_, 2, v___x_2651_);
lean_inc(v_ref_2622_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_ref_2622_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_PersistentArray_push___redArg(v_traces_2642_, v___x_2653_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2654_);
v___x_2656_ = v___x_2644_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2654_);
lean_ctor_set_uint64(v_reuseFailAlloc_2665_, sizeof(void*)*1, v_tid_2641_);
v___x_2656_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2658_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 4, v___x_2656_);
v___x_2658_ = v___x_2639_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_env_2630_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_nextMacroScope_2631_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_ngen_2632_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_auxDeclNGen_2633_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2664_, 5, v_cache_2634_);
lean_ctor_set(v_reuseFailAlloc_2664_, 6, v_messages_2635_);
lean_ctor_set(v_reuseFailAlloc_2664_, 7, v_infoState_2636_);
lean_ctor_set(v_reuseFailAlloc_2664_, 8, v_snapshotTasks_2637_);
v___x_2658_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = lean_st_ref_set(v___y_2620_, v___x_2658_);
v___x_2660_ = lean_box(0);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2660_);
v___x_2662_ = v___x_2626_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14___boxed(lean_object* v_cls_2669_, lean_object* v_msg_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14(v_cls_2669_, v_msg_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
if (lean_obj_tag(v_a_2677_) == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = l_List_reverse___redArg(v_a_2678_);
return v___x_2679_;
}
else
{
lean_object* v_head_2680_; lean_object* v_tail_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2692_; 
v_head_2680_ = lean_ctor_get(v_a_2677_, 0);
v_tail_2681_ = lean_ctor_get(v_a_2677_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2677_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2683_ = v_a_2677_;
v_isShared_2684_ = v_isSharedCheck_2692_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_tail_2681_);
lean_inc(v_head_2680_);
lean_dec(v_a_2677_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2692_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2685_ = l_Nat_reprFast(v_head_2680_);
v___x_2686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_ofFormat(v___x_2686_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v_a_2678_);
lean_ctor_set(v___x_2683_, 0, v___x_2687_);
v___x_2689_ = v___x_2683_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_a_2678_);
v___x_2689_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2677_ = v_tail_2681_;
v_a_2678_ = v___x_2689_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_argVars_2693_, size_t v_sz_2694_, size_t v_i_2695_, lean_object* v_bs_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_lt(v_i_2695_, v_sz_2694_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_bs_2696_);
return v___x_2703_;
}
else
{
lean_object* v_v_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_v_2704_ = lean_array_uget_borrowed(v_bs_2696_, v_i_2695_);
v___x_2705_ = l_Lean_instInhabitedExpr;
v___x_2706_ = lean_array_get_borrowed(v___x_2705_, v_argVars_2693_, v_v_2704_);
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___x_2706_);
v___x_2707_ = lean_infer_type(v___x_2706_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; lean_object* v_bs_x27_2710_; lean_object* v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref(v___x_2707_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v_bs_x27_2710_ = lean_array_uset(v_bs_2696_, v_i_2695_, v___x_2709_);
v___x_2711_ = l_Lean_indentExpr(v_a_2708_);
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2695_, v___x_2712_);
v___x_2714_ = lean_array_uset(v_bs_x27_2710_, v_i_2695_, v___x_2711_);
v_i_2695_ = v___x_2713_;
v_bs_2696_ = v___x_2714_;
goto _start;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec_ref(v_bs_2696_);
v_a_2716_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2707_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2707_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12___boxed(lean_object* v_argVars_2724_, lean_object* v_sz_2725_, lean_object* v_i_2726_, lean_object* v_bs_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
size_t v_sz_boxed_2733_; size_t v_i_boxed_2734_; lean_object* v_res_2735_; 
v_sz_boxed_2733_ = lean_unbox_usize(v_sz_2725_);
lean_dec(v_sz_2725_);
v_i_boxed_2734_ = lean_unbox_usize(v_i_2726_);
lean_dec(v_i_2726_);
v_res_2735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v_argVars_2724_, v_sz_boxed_2733_, v_i_boxed_2734_, v_bs_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec_ref(v_argVars_2724_);
return v_res_2735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4));
v___x_2745_ = l_Lean_stringToMessageData(v___x_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6));
v___x_2748_ = l_Lean_stringToMessageData(v___x_2747_);
return v___x_2748_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2752_, lean_object* v_fst_2753_, lean_object* v_fst_2754_, lean_object* v_inst_2755_, lean_object* v_a_2756_, lean_object* v_projInfo_x3f_2757_, lean_object* v_argVars_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
v___x_2765_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2752_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v_dummy_2767_; lean_object* v_nargs_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___x_2765_);
v_dummy_2767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2768_ = l_Lean_Expr_getAppNumArgs(v_a_2752_);
lean_inc(v_nargs_2768_);
v___x_2769_ = lean_mk_array(v_nargs_2768_, v_dummy_2767_);
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_sub(v_nargs_2768_, v___x_2770_);
lean_dec(v_nargs_2768_);
lean_inc_ref(v_a_2752_);
v___x_2772_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2752_, v___x_2769_, v___x_2771_);
v___x_2773_ = lean_array_get_size(v___x_2772_);
v___x_2774_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v___x_2773_);
v_sz_2776_ = lean_array_size(v___x_2772_);
v___x_2777_ = ((size_t)0ULL);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2766_, v_fst_2753_, v_argVars_2758_, v___x_2772_, v_sz_2776_, v___x_2777_, v___x_2775_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec_ref(v___x_2772_);
lean_dec(v_a_2766_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec_ref(v___x_2778_);
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2780_ = lean_array_get_size(v_fst_2753_);
v___x_2781_ = l_List_range(v___x_2780_);
v___x_2782_ = lean_box(0);
v___x_2783_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2754_, v___x_2781_, v___x_2782_);
v___x_2784_ = lean_array_mk(v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2779_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc_ref(v_inst_2755_);
v___x_2786_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2753_, v_argVars_2758_, v_inst_2755_, v_a_2756_, v_projInfo_x3f_2757_, v___x_2785_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v_fst_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2872_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v_fst_2788_ = lean_ctor_get(v_a_2787_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_a_2787_, 1);
lean_dec(v_unused_2873_);
v___x_2790_ = v_a_2787_;
v_isShared_2791_ = v_isSharedCheck_2872_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_fst_2788_);
lean_dec(v_a_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2872_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v_options_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_options_2853_ = lean_ctor_get(v___y_2762_, 2);
v___x_2854_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2855_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_dec_ref(v_a_2752_);
v___y_2793_ = v___y_2760_;
v___y_2794_ = v___y_2761_;
v___y_2795_ = v___y_2762_;
v___y_2796_ = v___y_2763_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2856_; lean_object* v_a_2857_; uint8_t v___x_2858_; 
v___x_2856_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2752_, v___y_2761_);
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = l_Lean_Expr_hasExprMVar(v_a_2857_);
if (v___x_2858_ == 0)
{
lean_dec(v_a_2857_);
v___y_2793_ = v___y_2760_;
v___y_2794_ = v___y_2761_;
v___y_2795_ = v___y_2762_;
v___y_2796_ = v___y_2763_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2790_);
lean_dec(v_fst_2788_);
lean_dec_ref(v_inst_2755_);
v___x_2859_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9);
v___x_2860_ = l_Lean_Expr_setPPExplicit(v_a_2857_, v___x_2858_);
v___x_2861_ = l_Lean_indentExpr(v___x_2860_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2859_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2862_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2792_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2852_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2798_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg(v___x_2797_, v___y_2795_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2852_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2852_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_unbox(v_a_2799_);
lean_dec(v_a_2799_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2805_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_del_object(v___x_2790_);
lean_dec_ref(v_inst_2755_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_fst_2788_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_fst_2788_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
else
{
size_t v_sz_2807_; lean_object* v___x_2808_; 
lean_del_object(v___x_2801_);
v_sz_2807_ = lean_array_size(v_fst_2788_);
lean_inc(v___y_2796_);
lean_inc_ref(v___y_2795_);
lean_inc(v___y_2794_);
lean_inc_ref(v___y_2793_);
lean_inc(v_fst_2788_);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v_argVars_2758_, v_sz_2807_, v___x_2777_, v_fst_2788_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3);
v___x_2811_ = l_Lean_MessageData_ofExpr(v_inst_2755_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 7);
lean_ctor_set(v___x_2790_, 1, v___x_2811_);
lean_ctor_set(v___x_2790_, 0, v___x_2810_);
v___x_2813_ = v___x_2790_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2814_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
lean_inc(v_fst_2788_);
v___x_2816_ = lean_array_to_list(v_fst_2788_);
v___x_2817_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2816_, v___x_2782_);
v___x_2818_ = l_Lean_MessageData_ofList(v___x_2817_);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2815_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7);
v___x_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_array_to_list(v_a_2809_);
v___x_2823_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2824_ = l_Lean_MessageData_joinSep(v___x_2822_, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2821_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__14(v___x_2797_, v___x_2825_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v___x_2826_, 0);
lean_dec(v_unused_2834_);
v___x_2828_ = v___x_2826_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_dec(v___x_2826_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v_fst_2788_);
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_fst_2788_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_fst_2788_);
v_a_2835_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2826_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2826_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_del_object(v___x_2790_);
lean_dec(v_fst_2788_);
lean_dec_ref(v_inst_2755_);
v_a_2844_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2808_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2808_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
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
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_inst_2755_);
lean_dec_ref(v_a_2752_);
v_a_2874_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2786_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2786_);
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
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_a_2756_);
lean_dec_ref(v_inst_2755_);
lean_dec_ref(v_a_2752_);
v_a_2882_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2778_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2778_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_a_2756_);
lean_dec_ref(v_inst_2755_);
lean_dec_ref(v_a_2752_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2890_, lean_object* v_fst_2891_, lean_object* v_fst_2892_, lean_object* v_inst_2893_, lean_object* v_a_2894_, lean_object* v_projInfo_x3f_2895_, lean_object* v_argVars_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2890_, v_fst_2891_, v_fst_2892_, v_inst_2893_, v_a_2894_, v_projInfo_x3f_2895_, v_argVars_2896_, v_x_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec_ref(v_x_2897_);
lean_dec_ref(v_argVars_2896_);
lean_dec(v_projInfo_x3f_2895_);
lean_dec_ref(v_fst_2892_);
lean_dec_ref(v_fst_2891_);
return v_res_2903_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2904_; uint64_t v___x_2905_; 
v___x_2904_ = 2;
v___x_2905_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2906_, lean_object* v_projInfo_x3f_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2913_; uint8_t v_foApprox_2914_; uint8_t v_ctxApprox_2915_; uint8_t v_quasiPatternApprox_2916_; uint8_t v_constApprox_2917_; uint8_t v_isDefEqStuckEx_2918_; uint8_t v_unificationHints_2919_; uint8_t v_proofIrrelevance_2920_; uint8_t v_assignSyntheticOpaque_2921_; uint8_t v_offsetCnstrs_2922_; uint8_t v_etaStruct_2923_; uint8_t v_univApprox_2924_; uint8_t v_iota_2925_; uint8_t v_beta_2926_; uint8_t v_proj_2927_; uint8_t v_zeta_2928_; uint8_t v_zetaDelta_2929_; uint8_t v_zetaUnused_2930_; uint8_t v_zetaHave_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3009_; 
v___x_2913_ = l_Lean_Meta_Context_config(v_a_2908_);
v_foApprox_2914_ = lean_ctor_get_uint8(v___x_2913_, 0);
v_ctxApprox_2915_ = lean_ctor_get_uint8(v___x_2913_, 1);
v_quasiPatternApprox_2916_ = lean_ctor_get_uint8(v___x_2913_, 2);
v_constApprox_2917_ = lean_ctor_get_uint8(v___x_2913_, 3);
v_isDefEqStuckEx_2918_ = lean_ctor_get_uint8(v___x_2913_, 4);
v_unificationHints_2919_ = lean_ctor_get_uint8(v___x_2913_, 5);
v_proofIrrelevance_2920_ = lean_ctor_get_uint8(v___x_2913_, 6);
v_assignSyntheticOpaque_2921_ = lean_ctor_get_uint8(v___x_2913_, 7);
v_offsetCnstrs_2922_ = lean_ctor_get_uint8(v___x_2913_, 8);
v_etaStruct_2923_ = lean_ctor_get_uint8(v___x_2913_, 10);
v_univApprox_2924_ = lean_ctor_get_uint8(v___x_2913_, 11);
v_iota_2925_ = lean_ctor_get_uint8(v___x_2913_, 12);
v_beta_2926_ = lean_ctor_get_uint8(v___x_2913_, 13);
v_proj_2927_ = lean_ctor_get_uint8(v___x_2913_, 14);
v_zeta_2928_ = lean_ctor_get_uint8(v___x_2913_, 15);
v_zetaDelta_2929_ = lean_ctor_get_uint8(v___x_2913_, 16);
v_zetaUnused_2930_ = lean_ctor_get_uint8(v___x_2913_, 17);
v_zetaHave_2931_ = lean_ctor_get_uint8(v___x_2913_, 18);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2933_ = v___x_2913_;
v_isShared_2934_ = v_isSharedCheck_3009_;
goto v_resetjp_2932_;
}
else
{
lean_dec(v___x_2913_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3009_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
uint8_t v_trackZetaDelta_2935_; lean_object* v_zetaDeltaSet_2936_; lean_object* v_lctx_2937_; lean_object* v_localInstances_2938_; lean_object* v_defEqCtx_x3f_2939_; lean_object* v_synthPendingDepth_2940_; lean_object* v_canUnfold_x3f_2941_; uint8_t v_univApprox_2942_; uint8_t v_inTypeClassResolution_2943_; uint8_t v_cacheInferType_2944_; uint8_t v___x_2945_; lean_object* v_config_2947_; 
v_trackZetaDelta_2935_ = lean_ctor_get_uint8(v_a_2908_, sizeof(void*)*7);
v_zetaDeltaSet_2936_ = lean_ctor_get(v_a_2908_, 1);
lean_inc(v_zetaDeltaSet_2936_);
v_lctx_2937_ = lean_ctor_get(v_a_2908_, 2);
lean_inc_ref(v_lctx_2937_);
v_localInstances_2938_ = lean_ctor_get(v_a_2908_, 3);
lean_inc_ref(v_localInstances_2938_);
v_defEqCtx_x3f_2939_ = lean_ctor_get(v_a_2908_, 4);
lean_inc(v_defEqCtx_x3f_2939_);
v_synthPendingDepth_2940_ = lean_ctor_get(v_a_2908_, 5);
lean_inc(v_synthPendingDepth_2940_);
v_canUnfold_x3f_2941_ = lean_ctor_get(v_a_2908_, 6);
lean_inc(v_canUnfold_x3f_2941_);
v_univApprox_2942_ = lean_ctor_get_uint8(v_a_2908_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2943_ = lean_ctor_get_uint8(v_a_2908_, sizeof(void*)*7 + 2);
v_cacheInferType_2944_ = lean_ctor_get_uint8(v_a_2908_, sizeof(void*)*7 + 3);
v___x_2945_ = 2;
if (v_isShared_2934_ == 0)
{
v_config_2947_ = v___x_2933_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 0, v_foApprox_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 1, v_ctxApprox_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 2, v_quasiPatternApprox_2916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 3, v_constApprox_2917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 4, v_isDefEqStuckEx_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 5, v_unificationHints_2919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 6, v_proofIrrelevance_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 7, v_assignSyntheticOpaque_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 8, v_offsetCnstrs_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 10, v_etaStruct_2923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 11, v_univApprox_2924_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 12, v_iota_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 13, v_beta_2926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 14, v_proj_2927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 15, v_zeta_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 16, v_zetaDelta_2929_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 17, v_zetaUnused_2930_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, 18, v_zetaHave_2931_);
v_config_2947_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
uint64_t v___x_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3000_; 
lean_ctor_set_uint8(v_config_2947_, 9, v___x_2945_);
v___x_2948_ = l_Lean_Meta_Context_configKey(v_a_2908_);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; lean_object* v_unused_3002_; lean_object* v_unused_3003_; lean_object* v_unused_3004_; lean_object* v_unused_3005_; lean_object* v_unused_3006_; lean_object* v_unused_3007_; 
v_unused_3001_ = lean_ctor_get(v_a_2908_, 6);
lean_dec(v_unused_3001_);
v_unused_3002_ = lean_ctor_get(v_a_2908_, 5);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_a_2908_, 4);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_a_2908_, 3);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_a_2908_, 2);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_a_2908_, 1);
lean_dec(v_unused_3006_);
v_unused_3007_ = lean_ctor_get(v_a_2908_, 0);
lean_dec(v_unused_3007_);
v___x_2950_ = v_a_2908_;
v_isShared_2951_ = v_isSharedCheck_3000_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v_a_2908_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3000_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
uint64_t v___x_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; uint64_t v_key_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2952_ = 2ULL;
v___x_2953_ = lean_uint64_shift_right(v___x_2948_, v___x_2952_);
v___x_2954_ = lean_uint64_shift_left(v___x_2953_, v___x_2952_);
v___x_2955_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2956_ = lean_uint64_lor(v___x_2954_, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2957_, 0, v_config_2947_);
lean_ctor_set_uint64(v___x_2957_, sizeof(void*)*1, v_key_2956_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2957_);
v___x_2959_ = v___x_2950_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_zetaDeltaSet_2936_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_lctx_2937_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_localInstances_2938_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_defEqCtx_x3f_2939_);
lean_ctor_set(v_reuseFailAlloc_2999_, 5, v_synthPendingDepth_2940_);
lean_ctor_set(v_reuseFailAlloc_2999_, 6, v_canUnfold_x3f_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*7, v_trackZetaDelta_2935_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*7 + 1, v_univApprox_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*7 + 3, v_cacheInferType_2944_);
v___x_2959_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
lean_inc(v_a_2911_);
lean_inc_ref(v_a_2910_);
lean_inc(v_a_2909_);
lean_inc_ref(v___x_2959_);
lean_inc_ref(v_inst_2906_);
v___x_2960_ = lean_infer_type(v_inst_2906_, v___x_2959_, v_a_2909_, v_a_2910_, v_a_2911_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = lean_box(0);
v___x_2963_ = 0;
lean_inc(v_a_2911_);
lean_inc_ref(v_a_2910_);
lean_inc(v_a_2909_);
lean_inc_ref(v___x_2959_);
lean_inc(v_a_2961_);
v___x_2964_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2961_, v___x_2962_, v___x_2963_, v___x_2959_, v_a_2909_, v_a_2910_, v_a_2911_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_snd_2966_; lean_object* v_fst_2967_; lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___x_2970_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref(v___x_2964_);
v_snd_2966_ = lean_ctor_get(v_a_2965_, 1);
lean_inc(v_snd_2966_);
v_fst_2967_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_fst_2967_);
lean_dec(v_a_2965_);
v_fst_2968_ = lean_ctor_get(v_snd_2966_, 0);
lean_inc(v_fst_2968_);
v_snd_2969_ = lean_ctor_get(v_snd_2966_, 1);
lean_inc(v_snd_2969_);
lean_dec(v_snd_2966_);
lean_inc(v_a_2911_);
lean_inc_ref(v_a_2910_);
lean_inc(v_a_2909_);
lean_inc_ref(v___x_2959_);
v___x_2970_ = lean_whnf(v_snd_2969_, v___x_2959_, v_a_2909_, v_a_2910_, v_a_2911_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___f_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
lean_inc(v_a_2961_);
v___f_2972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2972_, 0, v_a_2971_);
lean_closure_set(v___f_2972_, 1, v_fst_2967_);
lean_closure_set(v___f_2972_, 2, v_fst_2968_);
lean_closure_set(v___f_2972_, 3, v_inst_2906_);
lean_closure_set(v___f_2972_, 4, v_a_2961_);
lean_closure_set(v___f_2972_, 5, v_projInfo_x3f_2907_);
v___x_2973_ = 0;
v___x_2974_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2961_, v___f_2972_, v___x_2973_, v___x_2973_, v___x_2959_, v_a_2909_, v_a_2910_, v_a_2911_);
return v___x_2974_;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_fst_2968_);
lean_dec(v_fst_2967_);
lean_dec(v_a_2961_);
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec(v_projInfo_x3f_2907_);
lean_dec_ref(v_inst_2906_);
v_a_2975_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2970_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2970_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2961_);
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec(v_projInfo_x3f_2907_);
lean_dec_ref(v_inst_2906_);
v_a_2983_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2964_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2964_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec(v_projInfo_x3f_2907_);
lean_dec_ref(v_inst_2906_);
v_a_2991_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2960_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2960_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3010_, lean_object* v_projInfo_x3f_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3010_, v_projInfo_x3f_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3018_, lean_object* v___x_3019_, lean_object* v_a_3020_, lean_object* v_inst_3021_, lean_object* v_R_3022_, lean_object* v_a_3023_, lean_object* v_b_3024_, lean_object* v_c_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3018_, v___x_3019_, v_a_3020_, v_a_3023_, v_b_3024_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3032_, lean_object* v___x_3033_, lean_object* v_a_3034_, lean_object* v_inst_3035_, lean_object* v_R_3036_, lean_object* v_a_3037_, lean_object* v_b_3038_, lean_object* v_c_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3032_, v___x_3033_, v_a_3034_, v_inst_3035_, v_R_3036_, v_a_3037_, v_b_3038_, v_c_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec_ref(v_a_3034_);
lean_dec(v___x_3033_);
lean_dec(v_upperBound_3032_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3046_, lean_object* v_msg_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_msg_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3054_, v_msg_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v_env_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3065_ = lean_st_ref_get(v___y_3063_);
v_env_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc_ref(v_env_3066_);
lean_dec(v___x_3065_);
v___x_3067_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3066_, v_declName_3062_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3069_, v___y_3070_);
lean_dec(v___y_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3073_, v___y_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3086_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3087_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3093_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
lean_ctor_set(v___x_3093_, 3, v___x_3092_);
lean_ctor_set(v___x_3093_, 4, v___x_3092_);
lean_ctor_set(v___x_3093_, 5, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3094_, lean_object* v_b_3095_, uint8_t v_kind_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_currNamespace_3101_; lean_object* v___x_3102_; lean_object* v_env_3103_; lean_object* v_nextMacroScope_3104_; lean_object* v_ngen_3105_; lean_object* v_auxDeclNGen_3106_; lean_object* v_traceState_3107_; lean_object* v_messages_3108_; lean_object* v_infoState_3109_; lean_object* v_snapshotTasks_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3137_; 
v_currNamespace_3101_ = lean_ctor_get(v___y_3098_, 6);
lean_inc(v_currNamespace_3101_);
lean_dec_ref(v___y_3098_);
v___x_3102_ = lean_st_ref_take(v___y_3099_);
v_env_3103_ = lean_ctor_get(v___x_3102_, 0);
v_nextMacroScope_3104_ = lean_ctor_get(v___x_3102_, 1);
v_ngen_3105_ = lean_ctor_get(v___x_3102_, 2);
v_auxDeclNGen_3106_ = lean_ctor_get(v___x_3102_, 3);
v_traceState_3107_ = lean_ctor_get(v___x_3102_, 4);
v_messages_3108_ = lean_ctor_get(v___x_3102_, 6);
v_infoState_3109_ = lean_ctor_get(v___x_3102_, 7);
v_snapshotTasks_3110_ = lean_ctor_get(v___x_3102_, 8);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3102_, 5);
lean_dec(v_unused_3138_);
v___x_3112_ = v___x_3102_;
v_isShared_3113_ = v_isSharedCheck_3137_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_snapshotTasks_3110_);
lean_inc(v_infoState_3109_);
lean_inc(v_messages_3108_);
lean_inc(v_traceState_3107_);
lean_inc(v_auxDeclNGen_3106_);
lean_inc(v_ngen_3105_);
lean_inc(v_nextMacroScope_3104_);
lean_inc(v_env_3103_);
lean_dec(v___x_3102_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3137_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3103_, v_ext_3094_, v_b_3095_, v_kind_3096_, v_currNamespace_3101_);
v___x_3115_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 5, v___x_3115_);
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3117_ = v___x_3112_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_nextMacroScope_3104_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_ngen_3105_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_auxDeclNGen_3106_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_traceState_3107_);
lean_ctor_set(v_reuseFailAlloc_3136_, 5, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3136_, 6, v_messages_3108_);
lean_ctor_set(v_reuseFailAlloc_3136_, 7, v_infoState_3109_);
lean_ctor_set(v_reuseFailAlloc_3136_, 8, v_snapshotTasks_3110_);
v___x_3117_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v_mctx_3120_; lean_object* v_zetaDeltaFVarIds_3121_; lean_object* v_postponed_3122_; lean_object* v_diag_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3134_; 
v___x_3118_ = lean_st_ref_set(v___y_3099_, v___x_3117_);
v___x_3119_ = lean_st_ref_take(v___y_3097_);
v_mctx_3120_ = lean_ctor_get(v___x_3119_, 0);
v_zetaDeltaFVarIds_3121_ = lean_ctor_get(v___x_3119_, 2);
v_postponed_3122_ = lean_ctor_get(v___x_3119_, 3);
v_diag_3123_ = lean_ctor_get(v___x_3119_, 4);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3119_, 1);
lean_dec(v_unused_3135_);
v___x_3125_ = v___x_3119_;
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_diag_3123_);
lean_inc(v_postponed_3122_);
lean_inc(v_zetaDeltaFVarIds_3121_);
lean_inc(v_mctx_3120_);
lean_dec(v___x_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_mctx_3120_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_zetaDeltaFVarIds_3121_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_postponed_3122_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v_diag_3123_);
v___x_3129_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_st_ref_set(v___y_3097_, v___x_3129_);
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3139_, lean_object* v_b_3140_, lean_object* v_kind_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
uint8_t v_kind_boxed_3146_; lean_object* v_res_3147_; 
v_kind_boxed_3146_ = lean_unbox(v_kind_3141_);
v_res_3147_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3139_, v_b_3140_, v_kind_boxed_3146_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec(v___y_3142_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3148_, lean_object* v_00_u03b2_3149_, lean_object* v_00_u03c3_3150_, lean_object* v_ext_3151_, lean_object* v_b_3152_, uint8_t v_kind_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3151_, v_b_3152_, v_kind_3153_, v___y_3155_, v___y_3156_, v___y_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3160_, lean_object* v_00_u03b2_3161_, lean_object* v_00_u03c3_3162_, lean_object* v_ext_3163_, lean_object* v_b_3164_, lean_object* v_kind_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_kind_boxed_3171_; lean_object* v_res_3172_; 
v_kind_boxed_3171_ = lean_unbox(v_kind_3165_);
v_res_3172_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3160_, v_00_u03b2_3161_, v_00_u03c3_3162_, v_ext_3163_, v_b_3164_, v_kind_boxed_3171_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v_env_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3176_ = lean_st_ref_get(v___y_3174_);
v_env_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3176_);
v___x_3178_ = lean_get_reducibility_status(v_env_3177_, v_declName_3173_);
v___x_3179_ = lean_box(v___x_3178_);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3181_, v___y_3182_);
lean_dec(v___y_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3185_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
lean_ctor_set(v___x_3204_, 2, v___x_3203_);
lean_ctor_set(v___x_3204_, 3, v___x_3202_);
lean_ctor_set(v___x_3204_, 4, v___x_3202_);
lean_ctor_set(v___x_3204_, 5, v___x_3202_);
lean_ctor_set(v___x_3204_, 6, v___x_3202_);
lean_ctor_set(v___x_3204_, 7, v___x_3202_);
lean_ctor_set(v___x_3204_, 8, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_unsigned_to_nat(32u);
v___x_3206_ = lean_mk_empty_array_with_capacity(v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3208_ = ((size_t)5ULL);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_unsigned_to_nat(32u);
v___x_3211_ = lean_mk_empty_array_with_capacity(v___x_3210_);
v___x_3212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3213_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3211_);
lean_ctor_set(v___x_3213_, 2, v___x_3209_);
lean_ctor_set(v___x_3213_, 3, v___x_3209_);
lean_ctor_set_usize(v___x_3213_, 4, v___x_3208_);
return v___x_3213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3214_ = lean_box(1);
v___x_3215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___x_3215_);
lean_ctor_set(v___x_3217_, 2, v___x_3214_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3220_ = l_Lean_stringToMessageData(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3226_ = l_Lean_stringToMessageData(v___x_3225_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3229_ = l_Lean_stringToMessageData(v___x_3228_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3238_ = l_Lean_stringToMessageData(v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3239_, lean_object* v_declHint_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; lean_object* v_env_3244_; uint8_t v___x_3245_; 
v___x_3243_ = lean_st_ref_get(v___y_3241_);
v_env_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref(v_env_3244_);
lean_dec(v___x_3243_);
v___x_3245_ = l_Lean_Name_isAnonymous(v_declHint_3240_);
if (v___x_3245_ == 0)
{
uint8_t v_isExporting_3246_; 
v_isExporting_3246_ = lean_ctor_get_uint8(v_env_3244_, sizeof(void*)*8);
if (v_isExporting_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_env_3244_);
lean_dec(v_declHint_3240_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_msg_3239_);
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
lean_inc_ref(v_env_3244_);
v___x_3248_ = l_Lean_Environment_setExporting(v_env_3244_, v___x_3245_);
lean_inc(v_declHint_3240_);
lean_inc_ref(v___x_3248_);
v___x_3249_ = l_Lean_Environment_contains(v___x_3248_, v_declHint_3240_, v_isExporting_3246_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref(v___x_3248_);
lean_dec_ref(v_env_3244_);
lean_dec(v_declHint_3240_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_msg_3239_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v_c_3256_; lean_object* v___x_3257_; 
v___x_3251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3253_ = l_Lean_Options_empty;
v___x_3254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3248_);
lean_ctor_set(v___x_3254_, 1, v___x_3251_);
lean_ctor_set(v___x_3254_, 2, v___x_3252_);
lean_ctor_set(v___x_3254_, 3, v___x_3253_);
lean_inc(v_declHint_3240_);
v___x_3255_ = l_Lean_MessageData_ofConstName(v_declHint_3240_, v___x_3245_);
v_c_3256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3256_, 0, v___x_3254_);
lean_ctor_set(v_c_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3244_, v_declHint_3240_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref(v_env_3244_);
lean_dec(v_declHint_3240_);
v___x_3258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set(v___x_3259_, 1, v_c_3256_);
v___x_3260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = l_Lean_MessageData_note(v___x_3261_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_msg_3239_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
return v___x_3264_;
}
else
{
lean_object* v_val_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3300_; 
v_val_3265_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3267_ = v___x_3257_;
v_isShared_3268_ = v_isSharedCheck_3300_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_val_3265_);
lean_dec(v___x_3257_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3300_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v_mod_3272_; uint8_t v___x_3273_; 
v___x_3269_ = lean_box(0);
v___x_3270_ = l_Lean_Environment_header(v_env_3244_);
lean_dec_ref(v_env_3244_);
v___x_3271_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3270_);
v_mod_3272_ = lean_array_get(v___x_3269_, v___x_3271_, v_val_3265_);
lean_dec(v_val_3265_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = l_Lean_isPrivateName(v_declHint_3240_);
lean_dec(v_declHint_3240_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v_c_3256_);
v___x_3276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = l_Lean_MessageData_ofName(v_mod_3272_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_MessageData_note(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_msg_3239_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3283_);
v___x_3285_ = v___x_3267_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3287_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v_c_3256_);
v___x_3289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_MessageData_ofName(v_mod_3272_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_MessageData_note(v___x_3294_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_msg_3239_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3296_);
v___x_3298_ = v___x_3267_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3301_; 
lean_dec_ref(v_env_3244_);
lean_dec(v_declHint_3240_);
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_msg_3239_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3302_, lean_object* v_declHint_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3302_, v_declHint_3303_, v___y_3304_);
lean_dec(v___y_3304_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3307_, lean_object* v_declHint_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3324_; 
v___x_3314_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3307_, v_declHint_3308_, v___y_3312_);
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3324_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3324_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3319_ = l_Lean_unknownIdentifierMessageTag;
v___x_3320_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v_a_3315_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3320_);
v___x_3322_ = v___x_3317_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3325_, lean_object* v_declHint_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3325_, v_declHint_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3333_, lean_object* v_msg_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_fileName_3340_; lean_object* v_fileMap_3341_; lean_object* v_options_3342_; lean_object* v_currRecDepth_3343_; lean_object* v_maxRecDepth_3344_; lean_object* v_ref_3345_; lean_object* v_currNamespace_3346_; lean_object* v_openDecls_3347_; lean_object* v_initHeartbeats_3348_; lean_object* v_maxHeartbeats_3349_; lean_object* v_quotContext_3350_; lean_object* v_currMacroScope_3351_; uint8_t v_diag_3352_; lean_object* v_cancelTk_x3f_3353_; uint8_t v_suppressElabErrors_3354_; lean_object* v_inheritedTraceOptions_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3364_; 
v_fileName_3340_ = lean_ctor_get(v___y_3337_, 0);
v_fileMap_3341_ = lean_ctor_get(v___y_3337_, 1);
v_options_3342_ = lean_ctor_get(v___y_3337_, 2);
v_currRecDepth_3343_ = lean_ctor_get(v___y_3337_, 3);
v_maxRecDepth_3344_ = lean_ctor_get(v___y_3337_, 4);
v_ref_3345_ = lean_ctor_get(v___y_3337_, 5);
v_currNamespace_3346_ = lean_ctor_get(v___y_3337_, 6);
v_openDecls_3347_ = lean_ctor_get(v___y_3337_, 7);
v_initHeartbeats_3348_ = lean_ctor_get(v___y_3337_, 8);
v_maxHeartbeats_3349_ = lean_ctor_get(v___y_3337_, 9);
v_quotContext_3350_ = lean_ctor_get(v___y_3337_, 10);
v_currMacroScope_3351_ = lean_ctor_get(v___y_3337_, 11);
v_diag_3352_ = lean_ctor_get_uint8(v___y_3337_, sizeof(void*)*14);
v_cancelTk_x3f_3353_ = lean_ctor_get(v___y_3337_, 12);
v_suppressElabErrors_3354_ = lean_ctor_get_uint8(v___y_3337_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3355_ = lean_ctor_get(v___y_3337_, 13);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___y_3337_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3357_ = v___y_3337_;
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_inheritedTraceOptions_3355_);
lean_inc(v_cancelTk_x3f_3353_);
lean_inc(v_currMacroScope_3351_);
lean_inc(v_quotContext_3350_);
lean_inc(v_maxHeartbeats_3349_);
lean_inc(v_initHeartbeats_3348_);
lean_inc(v_openDecls_3347_);
lean_inc(v_currNamespace_3346_);
lean_inc(v_ref_3345_);
lean_inc(v_maxRecDepth_3344_);
lean_inc(v_currRecDepth_3343_);
lean_inc(v_options_3342_);
lean_inc(v_fileMap_3341_);
lean_inc(v_fileName_3340_);
lean_dec(v___y_3337_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_ref_3359_; lean_object* v___x_3361_; 
v_ref_3359_ = l_Lean_replaceRef(v_ref_3333_, v_ref_3345_);
lean_dec(v_ref_3345_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 5, v_ref_3359_);
v___x_3361_ = v___x_3357_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_fileName_3340_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_fileMap_3341_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_options_3342_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_currRecDepth_3343_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_maxRecDepth_3344_);
lean_ctor_set(v_reuseFailAlloc_3363_, 5, v_ref_3359_);
lean_ctor_set(v_reuseFailAlloc_3363_, 6, v_currNamespace_3346_);
lean_ctor_set(v_reuseFailAlloc_3363_, 7, v_openDecls_3347_);
lean_ctor_set(v_reuseFailAlloc_3363_, 8, v_initHeartbeats_3348_);
lean_ctor_set(v_reuseFailAlloc_3363_, 9, v_maxHeartbeats_3349_);
lean_ctor_set(v_reuseFailAlloc_3363_, 10, v_quotContext_3350_);
lean_ctor_set(v_reuseFailAlloc_3363_, 11, v_currMacroScope_3351_);
lean_ctor_set(v_reuseFailAlloc_3363_, 12, v_cancelTk_x3f_3353_);
lean_ctor_set(v_reuseFailAlloc_3363_, 13, v_inheritedTraceOptions_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3363_, sizeof(void*)*14, v_diag_3352_);
lean_ctor_set_uint8(v_reuseFailAlloc_3363_, sizeof(void*)*14 + 1, v_suppressElabErrors_3354_);
v___x_3361_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3334_, v___y_3335_, v___y_3336_, v___x_3361_, v___y_3338_);
lean_dec_ref(v___x_3361_);
return v___x_3362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3365_, lean_object* v_msg_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3365_, v_msg_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v_ref_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3373_, lean_object* v_msg_3374_, lean_object* v_declHint_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v_a_3382_; lean_object* v___x_3383_; 
v___x_3381_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3374_, v_declHint_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3373_, v_a_3382_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3384_, lean_object* v_msg_3385_, lean_object* v_declHint_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3384_, v_msg_3385_, v_declHint_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v_ref_3384_);
return v_res_3392_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3396_, lean_object* v_constName_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3403_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3404_ = 0;
lean_inc(v_constName_3397_);
v___x_3405_ = l_Lean_MessageData_ofConstName(v_constName_3397_, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3403_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3396_, v___x_3408_, v_constName_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3410_, lean_object* v_constName_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3410_, v_constName_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v_ref_3410_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_ref_3424_; lean_object* v___x_3425_; 
v_ref_3424_ = lean_ctor_get(v___y_3421_, 5);
lean_inc(v_ref_3424_);
v___x_3425_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3424_, v_constName_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v_ref_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; lean_object* v_env_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3439_ = lean_st_ref_get(v___y_3437_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_ref(v_env_3440_);
lean_dec(v___x_3439_);
v___x_3441_ = 0;
lean_inc(v_constName_3433_);
v___x_3442_ = l_Lean_Environment_find_x3f(v_env_3440_, v_constName_3433_, v___x_3441_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3443_;
}
else
{
lean_object* v_val_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v___y_3436_);
lean_dec(v_constName_3433_);
v_val_3444_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_val_3444_);
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 0);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_val_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3466_, uint8_t v_suppressElabErrors_3467_, lean_object* v_x_3468_){
_start:
{
if (lean_obj_tag(v_x_3468_) == 1)
{
lean_object* v_pre_3469_; 
v_pre_3469_ = lean_ctor_get(v_x_3468_, 0);
switch(lean_obj_tag(v_pre_3469_))
{
case 1:
{
lean_object* v_pre_3470_; 
v_pre_3470_ = lean_ctor_get(v_pre_3469_, 0);
switch(lean_obj_tag(v_pre_3470_))
{
case 0:
{
lean_object* v_str_3471_; lean_object* v_str_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v_str_3471_ = lean_ctor_get(v_x_3468_, 1);
v_str_3472_ = lean_ctor_get(v_pre_3469_, 1);
v___x_3473_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3474_ = lean_string_dec_eq(v_str_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3476_ = lean_string_dec_eq(v_str_3472_, v___x_3475_);
if (v___x_3476_ == 0)
{
return v___y_3466_;
}
else
{
lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3478_ = lean_string_dec_eq(v_str_3471_, v___x_3477_);
if (v___x_3478_ == 0)
{
return v___y_3466_;
}
else
{
return v_suppressElabErrors_3467_;
}
}
}
else
{
lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3480_ = lean_string_dec_eq(v_str_3471_, v___x_3479_);
if (v___x_3480_ == 0)
{
return v___y_3466_;
}
else
{
return v_suppressElabErrors_3467_;
}
}
}
case 1:
{
lean_object* v_pre_3481_; 
v_pre_3481_ = lean_ctor_get(v_pre_3470_, 0);
if (lean_obj_tag(v_pre_3481_) == 0)
{
lean_object* v_str_3482_; lean_object* v_str_3483_; lean_object* v_str_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v_str_3482_ = lean_ctor_get(v_x_3468_, 1);
v_str_3483_ = lean_ctor_get(v_pre_3469_, 1);
v_str_3484_ = lean_ctor_get(v_pre_3470_, 1);
v___x_3485_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3486_ = lean_string_dec_eq(v_str_3484_, v___x_3485_);
if (v___x_3486_ == 0)
{
return v___y_3466_;
}
else
{
lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3487_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3488_ = lean_string_dec_eq(v_str_3483_, v___x_3487_);
if (v___x_3488_ == 0)
{
return v___y_3466_;
}
else
{
lean_object* v___x_3489_; uint8_t v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3490_ = lean_string_dec_eq(v_str_3482_, v___x_3489_);
if (v___x_3490_ == 0)
{
return v___y_3466_;
}
else
{
return v_suppressElabErrors_3467_;
}
}
}
}
else
{
return v___y_3466_;
}
}
default: 
{
return v___y_3466_;
}
}
}
case 0:
{
lean_object* v_str_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v_str_3491_ = lean_ctor_get(v_x_3468_, 1);
v___x_3492_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___redArg___closed__0));
v___x_3493_ = lean_string_dec_eq(v_str_3491_, v___x_3492_);
if (v___x_3493_ == 0)
{
return v___y_3466_;
}
else
{
return v_suppressElabErrors_3467_;
}
}
default: 
{
return v___y_3466_;
}
}
}
else
{
return v___y_3466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3494_, lean_object* v_suppressElabErrors_3495_, lean_object* v_x_3496_){
_start:
{
uint8_t v___y_8293__boxed_3497_; uint8_t v_suppressElabErrors_boxed_3498_; uint8_t v_res_3499_; lean_object* v_r_3500_; 
v___y_8293__boxed_3497_ = lean_unbox(v___y_3494_);
v_suppressElabErrors_boxed_3498_ = lean_unbox(v_suppressElabErrors_3495_);
v_res_3499_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8293__boxed_3497_, v_suppressElabErrors_boxed_3498_, v_x_3496_);
lean_dec(v_x_3496_);
v_r_3500_ = lean_box(v_res_3499_);
return v_r_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3501_, lean_object* v_msgData_3502_, uint8_t v_severity_3503_, uint8_t v_isSilent_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3547_; uint8_t v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3572_; uint8_t v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; uint8_t v___x_3594_; uint8_t v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; uint8_t v___y_3602_; uint8_t v___y_3604_; uint8_t v___x_3619_; 
v___x_3594_ = 2;
v___x_3619_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3503_, v___x_3594_);
if (v___x_3619_ == 0)
{
v___y_3604_ = v___x_3619_;
goto v___jp_3603_;
}
else
{
uint8_t v___x_3620_; 
lean_inc_ref(v_msgData_3502_);
v___x_3620_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3502_);
v___y_3604_ = v___x_3620_;
goto v___jp_3603_;
}
v___jp_3510_:
{
lean_object* v___x_3520_; lean_object* v_currNamespace_3521_; lean_object* v_openDecls_3522_; lean_object* v_env_3523_; lean_object* v_nextMacroScope_3524_; lean_object* v_ngen_3525_; lean_object* v_auxDeclNGen_3526_; lean_object* v_traceState_3527_; lean_object* v_cache_3528_; lean_object* v_messages_3529_; lean_object* v_infoState_3530_; lean_object* v_snapshotTasks_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3545_; 
v___x_3520_ = lean_st_ref_take(v___y_3519_);
v_currNamespace_3521_ = lean_ctor_get(v___y_3518_, 6);
lean_inc(v_currNamespace_3521_);
v_openDecls_3522_ = lean_ctor_get(v___y_3518_, 7);
lean_inc(v_openDecls_3522_);
lean_dec_ref(v___y_3518_);
v_env_3523_ = lean_ctor_get(v___x_3520_, 0);
v_nextMacroScope_3524_ = lean_ctor_get(v___x_3520_, 1);
v_ngen_3525_ = lean_ctor_get(v___x_3520_, 2);
v_auxDeclNGen_3526_ = lean_ctor_get(v___x_3520_, 3);
v_traceState_3527_ = lean_ctor_get(v___x_3520_, 4);
v_cache_3528_ = lean_ctor_get(v___x_3520_, 5);
v_messages_3529_ = lean_ctor_get(v___x_3520_, 6);
v_infoState_3530_ = lean_ctor_get(v___x_3520_, 7);
v_snapshotTasks_3531_ = lean_ctor_get(v___x_3520_, 8);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3533_ = v___x_3520_;
v_isShared_3534_ = v_isSharedCheck_3545_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snapshotTasks_3531_);
lean_inc(v_infoState_3530_);
lean_inc(v_messages_3529_);
lean_inc(v_cache_3528_);
lean_inc(v_traceState_3527_);
lean_inc(v_auxDeclNGen_3526_);
lean_inc(v_ngen_3525_);
lean_inc(v_nextMacroScope_3524_);
lean_inc(v_env_3523_);
lean_dec(v___x_3520_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3545_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_currNamespace_3521_);
lean_ctor_set(v___x_3535_, 1, v_openDecls_3522_);
v___x_3536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___y_3514_);
v___x_3537_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3537_, 0, v___y_3517_);
lean_ctor_set(v___x_3537_, 1, v___y_3515_);
lean_ctor_set(v___x_3537_, 2, v___y_3511_);
lean_ctor_set(v___x_3537_, 3, v___y_3512_);
lean_ctor_set(v___x_3537_, 4, v___x_3536_);
lean_ctor_set_uint8(v___x_3537_, sizeof(void*)*5, v___y_3513_);
lean_ctor_set_uint8(v___x_3537_, sizeof(void*)*5 + 1, v___y_3516_);
lean_ctor_set_uint8(v___x_3537_, sizeof(void*)*5 + 2, v_isSilent_3504_);
v___x_3538_ = l_Lean_MessageLog_add(v___x_3537_, v_messages_3529_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 6, v___x_3538_);
v___x_3540_ = v___x_3533_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_env_3523_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_nextMacroScope_3524_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_ngen_3525_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_auxDeclNGen_3526_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_traceState_3527_);
lean_ctor_set(v_reuseFailAlloc_3544_, 5, v_cache_3528_);
lean_ctor_set(v_reuseFailAlloc_3544_, 6, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3544_, 7, v_infoState_3530_);
lean_ctor_set(v_reuseFailAlloc_3544_, 8, v_snapshotTasks_3531_);
v___x_3540_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_st_ref_set(v___y_3519_, v___x_3540_);
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
}
v___jp_3546_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3570_; 
v___x_3555_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3502_);
v___x_3556_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3555_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3570_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3570_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_inc_ref(v___y_3553_);
v___x_3561_ = l_Lean_FileMap_toPosition(v___y_3553_, v___y_3550_);
lean_dec(v___y_3550_);
v___x_3562_ = l_Lean_FileMap_toPosition(v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
v___x_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
v___x_3564_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3548_ == 0)
{
lean_del_object(v___x_3559_);
lean_dec_ref(v___y_3547_);
v___y_3511_ = v___x_3563_;
v___y_3512_ = v___x_3564_;
v___y_3513_ = v___y_3549_;
v___y_3514_ = v_a_3557_;
v___y_3515_ = v___x_3561_;
v___y_3516_ = v___y_3552_;
v___y_3517_ = v___y_3551_;
v___y_3518_ = v___y_3507_;
v___y_3519_ = v___y_3508_;
goto v___jp_3510_;
}
else
{
uint8_t v___x_3565_; 
lean_inc(v_a_3557_);
v___x_3565_ = l_Lean_MessageData_hasTag(v___y_3547_, v_a_3557_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref(v___x_3561_);
lean_dec(v_a_3557_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v___y_3507_);
v___x_3566_ = lean_box(0);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3566_);
v___x_3568_ = v___x_3559_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
else
{
lean_del_object(v___x_3559_);
v___y_3511_ = v___x_3563_;
v___y_3512_ = v___x_3564_;
v___y_3513_ = v___y_3549_;
v___y_3514_ = v_a_3557_;
v___y_3515_ = v___x_3561_;
v___y_3516_ = v___y_3552_;
v___y_3517_ = v___y_3551_;
v___y_3518_ = v___y_3507_;
v___y_3519_ = v___y_3508_;
goto v___jp_3510_;
}
}
}
}
v___jp_3571_:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Syntax_getTailPos_x3f(v___y_3578_, v___y_3574_);
lean_dec(v___y_3578_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_inc(v___y_3579_);
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___y_3573_;
v___y_3549_ = v___y_3574_;
v___y_3550_ = v___y_3579_;
v___y_3551_ = v___y_3577_;
v___y_3552_ = v___y_3576_;
v___y_3553_ = v___y_3575_;
v___y_3554_ = v___y_3579_;
goto v___jp_3546_;
}
else
{
lean_object* v_val_3581_; 
v_val_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v___x_3580_);
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___y_3573_;
v___y_3549_ = v___y_3574_;
v___y_3550_ = v___y_3579_;
v___y_3551_ = v___y_3577_;
v___y_3552_ = v___y_3576_;
v___y_3553_ = v___y_3575_;
v___y_3554_ = v_val_3581_;
goto v___jp_3546_;
}
}
v___jp_3582_:
{
lean_object* v_ref_3590_; lean_object* v___x_3591_; 
v_ref_3590_ = l_Lean_replaceRef(v_ref_3501_, v___y_3585_);
lean_dec(v___y_3585_);
v___x_3591_ = l_Lean_Syntax_getPos_x3f(v_ref_3590_, v___y_3586_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_unsigned_to_nat(0u);
v___y_3572_ = v___y_3583_;
v___y_3573_ = v___y_3584_;
v___y_3574_ = v___y_3586_;
v___y_3575_ = v___y_3588_;
v___y_3576_ = v___y_3589_;
v___y_3577_ = v___y_3587_;
v___y_3578_ = v_ref_3590_;
v___y_3579_ = v___x_3592_;
goto v___jp_3571_;
}
else
{
lean_object* v_val_3593_; 
v_val_3593_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_val_3593_);
lean_dec_ref(v___x_3591_);
v___y_3572_ = v___y_3583_;
v___y_3573_ = v___y_3584_;
v___y_3574_ = v___y_3586_;
v___y_3575_ = v___y_3588_;
v___y_3576_ = v___y_3589_;
v___y_3577_ = v___y_3587_;
v___y_3578_ = v_ref_3590_;
v___y_3579_ = v_val_3593_;
goto v___jp_3571_;
}
}
v___jp_3595_:
{
if (v___y_3602_ == 0)
{
v___y_3583_ = v___y_3597_;
v___y_3584_ = v___y_3596_;
v___y_3585_ = v___y_3598_;
v___y_3586_ = v___y_3601_;
v___y_3587_ = v___y_3600_;
v___y_3588_ = v___y_3599_;
v___y_3589_ = v_severity_3503_;
goto v___jp_3582_;
}
else
{
v___y_3583_ = v___y_3597_;
v___y_3584_ = v___y_3596_;
v___y_3585_ = v___y_3598_;
v___y_3586_ = v___y_3601_;
v___y_3587_ = v___y_3600_;
v___y_3588_ = v___y_3599_;
v___y_3589_ = v___x_3594_;
goto v___jp_3582_;
}
}
v___jp_3603_:
{
if (v___y_3604_ == 0)
{
lean_object* v_fileName_3605_; lean_object* v_fileMap_3606_; lean_object* v_options_3607_; lean_object* v_ref_3608_; uint8_t v_suppressElabErrors_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___f_3612_; uint8_t v___x_3613_; uint8_t v___x_3614_; 
v_fileName_3605_ = lean_ctor_get(v___y_3507_, 0);
v_fileMap_3606_ = lean_ctor_get(v___y_3507_, 1);
v_options_3607_ = lean_ctor_get(v___y_3507_, 2);
v_ref_3608_ = lean_ctor_get(v___y_3507_, 5);
v_suppressElabErrors_3609_ = lean_ctor_get_uint8(v___y_3507_, sizeof(void*)*14 + 1);
v___x_3610_ = lean_box(v___y_3604_);
v___x_3611_ = lean_box(v_suppressElabErrors_3609_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3612_, 0, v___x_3610_);
lean_closure_set(v___f_3612_, 1, v___x_3611_);
v___x_3613_ = 1;
v___x_3614_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3503_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_inc_ref(v_fileName_3605_);
lean_inc_ref(v_fileMap_3606_);
lean_inc(v_ref_3608_);
v___y_3596_ = v_suppressElabErrors_3609_;
v___y_3597_ = v___f_3612_;
v___y_3598_ = v_ref_3608_;
v___y_3599_ = v_fileMap_3606_;
v___y_3600_ = v_fileName_3605_;
v___y_3601_ = v___y_3604_;
v___y_3602_ = v___x_3614_;
goto v___jp_3595_;
}
else
{
lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3615_ = l_Lean_warningAsError;
v___x_3616_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3607_, v___x_3615_);
lean_inc_ref(v_fileName_3605_);
lean_inc_ref(v_fileMap_3606_);
lean_inc(v_ref_3608_);
v___y_3596_ = v_suppressElabErrors_3609_;
v___y_3597_ = v___f_3612_;
v___y_3598_ = v_ref_3608_;
v___y_3599_ = v_fileMap_3606_;
v___y_3600_ = v_fileName_3605_;
v___y_3601_ = v___y_3604_;
v___y_3602_ = v___x_3616_;
goto v___jp_3595_;
}
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec_ref(v___y_3507_);
lean_dec_ref(v_msgData_3502_);
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3621_, lean_object* v_msgData_3622_, lean_object* v_severity_3623_, lean_object* v_isSilent_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v_severity_boxed_3630_; uint8_t v_isSilent_boxed_3631_; lean_object* v_res_3632_; 
v_severity_boxed_3630_ = lean_unbox(v_severity_3623_);
v_isSilent_boxed_3631_ = lean_unbox(v_isSilent_3624_);
v_res_3632_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3621_, v_msgData_3622_, v_severity_boxed_3630_, v_isSilent_boxed_3631_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_ref_3621_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3633_, uint8_t v_severity_3634_, uint8_t v_isSilent_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_ref_3641_; lean_object* v___x_3642_; 
v_ref_3641_ = lean_ctor_get(v___y_3638_, 5);
lean_inc(v_ref_3641_);
v___x_3642_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3641_, v_msgData_3633_, v_severity_3634_, v_isSilent_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v_ref_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3643_, lean_object* v_severity_3644_, lean_object* v_isSilent_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_severity_boxed_3651_; uint8_t v_isSilent_boxed_3652_; lean_object* v_res_3653_; 
v_severity_boxed_3651_ = lean_unbox(v_severity_3644_);
v_isSilent_boxed_3652_ = lean_unbox(v_isSilent_3645_);
v_res_3653_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3643_, v_severity_boxed_3651_, v_isSilent_boxed_3652_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
uint8_t v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = 1;
v___x_3661_ = 0;
v___x_3662_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3654_, v___x_3660_, v___x_3661_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; lean_object* v_env_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3676_ = lean_st_ref_get(v___y_3674_);
v_env_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc_ref(v_env_3677_);
lean_dec(v___x_3676_);
v___x_3678_ = 0;
lean_inc(v_constName_3670_);
v___x_3679_ = l_Lean_Environment_findConstVal_x3f(v_env_3677_, v_constName_3670_, v___x_3678_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
return v___x_3680_;
}
else
{
lean_object* v_val_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___y_3673_);
lean_dec(v_constName_3670_);
v_val_3681_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3679_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_val_3681_);
lean_dec(v___x_3679_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set_tag(v___x_3683_, 0);
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_val_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
if (lean_obj_tag(v_a_3696_) == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = l_List_reverse___redArg(v_a_3697_);
return v___x_3698_;
}
else
{
lean_object* v_head_3699_; lean_object* v_tail_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3709_; 
v_head_3699_ = lean_ctor_get(v_a_3696_, 0);
v_tail_3700_ = lean_ctor_get(v_a_3696_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3696_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3702_ = v_a_3696_;
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_tail_3700_);
lean_inc(v_head_3699_);
lean_dec(v_a_3696_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = l_Lean_mkLevelParam(v_head_3699_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v_a_3697_);
lean_ctor_set(v___x_3702_, 0, v___x_3704_);
v___x_3706_ = v___x_3702_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_a_3697_);
v___x_3706_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
v_a_3696_ = v_tail_3700_;
v_a_3697_ = v___x_3706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
lean_inc(v_constName_3710_);
v___x_3716_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3728_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v_levelParams_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v_levelParams_3721_ = lean_ctor_get(v_a_3717_, 1);
lean_inc(v_levelParams_3721_);
lean_dec(v_a_3717_);
v___x_3722_ = lean_box(0);
v___x_3723_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_3721_, v___x_3722_);
v___x_3724_ = l_Lean_mkConst(v_constName_3710_, v___x_3723_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3724_);
v___x_3726_ = v___x_3719_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v_constName_3710_);
v_a_3729_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3716_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3716_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
return v_res_3743_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_3746_ = l_Lean_stringToMessageData(v___x_3745_);
return v___x_3746_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_3749_ = l_Lean_stringToMessageData(v___x_3748_);
return v___x_3749_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_3752_ = l_Lean_stringToMessageData(v___x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_3753_, uint8_t v_attrKind_3754_, lean_object* v_prio_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3761_; 
lean_inc_ref(v_a_3758_);
lean_inc(v_declName_3753_);
v___x_3761_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_3753_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
lean_inc(v_a_3759_);
lean_inc_ref(v_a_3758_);
lean_inc(v_a_3757_);
lean_inc_ref(v_a_3756_);
lean_inc(v_a_3762_);
v___x_3763_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_3762_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___x_3792_; lean_object* v_a_3793_; uint8_t v___x_3794_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
lean_inc(v_declName_3753_);
v___x_3792_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3753_, v_a_3759_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3792_);
v___x_3794_ = lean_unbox(v_a_3793_);
lean_dec(v_a_3793_);
switch(v___x_3794_)
{
case 0:
{
v___y_3766_ = v_a_3756_;
v___y_3767_ = v_a_3757_;
v___y_3768_ = v_a_3758_;
v___y_3769_ = v_a_3759_;
goto v___jp_3765_;
}
case 3:
{
v___y_3766_ = v_a_3756_;
v___y_3767_ = v_a_3757_;
v___y_3768_ = v_a_3758_;
v___y_3769_ = v_a_3759_;
goto v___jp_3765_;
}
default: 
{
lean_object* v___x_3795_; 
lean_inc_ref(v_a_3758_);
lean_inc(v_declName_3753_);
v___x_3795_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_3753_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; uint8_t v___x_3797_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = l_Lean_ConstantInfo_isDefinition(v_a_3796_);
lean_dec(v_a_3796_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v_env_3799_; uint8_t v___x_3800_; 
v___x_3798_ = lean_st_ref_get(v_a_3759_);
v_env_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc_ref(v_env_3799_);
lean_dec(v___x_3798_);
lean_inc(v_declName_3753_);
v___x_3800_ = l_Lean_wasOriginallyDefn(v_env_3799_, v_declName_3753_);
if (v___x_3800_ == 0)
{
v___y_3766_ = v_a_3756_;
v___y_3767_ = v_a_3757_;
v___y_3768_ = v_a_3758_;
v___y_3769_ = v_a_3759_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3801_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3753_);
v___x_3802_ = l_Lean_MessageData_ofName(v_declName_3753_);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_3805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
lean_inc_ref(v_a_3758_);
v___x_3806_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3805_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref(v___x_3806_);
v___y_3766_ = v_a_3756_;
v___y_3767_ = v_a_3757_;
v___y_3768_ = v_a_3758_;
v___y_3769_ = v_a_3759_;
goto v___jp_3765_;
}
else
{
lean_dec(v_a_3764_);
lean_dec(v_a_3762_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3807_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3753_);
v___x_3808_ = l_Lean_MessageData_ofName(v_declName_3753_);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
lean_inc_ref(v_a_3758_);
v___x_3812_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3811_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_dec_ref(v___x_3812_);
v___y_3766_ = v_a_3756_;
v___y_3767_ = v_a_3757_;
v___y_3768_ = v_a_3758_;
v___y_3769_ = v_a_3759_;
goto v___jp_3765_;
}
else
{
lean_dec(v_a_3764_);
lean_dec(v_a_3762_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
return v___x_3812_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v_a_3764_);
lean_dec(v_a_3762_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
v_a_3813_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3795_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3795_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
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
}
v___jp_3765_:
{
lean_object* v___x_3770_; lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3791_; 
lean_inc(v_declName_3753_);
v___x_3770_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3753_, v___y_3769_);
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3791_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3791_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; 
lean_inc(v___y_3769_);
lean_inc_ref(v___y_3768_);
lean_inc(v___y_3767_);
lean_inc(v_a_3762_);
v___x_3775_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_3762_, v_a_3771_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3775_);
v___x_3777_ = l_Lean_Meta_instanceExtension;
if (v_isShared_3774_ == 0)
{
lean_ctor_set_tag(v___x_3773_, 1);
lean_ctor_set(v___x_3773_, 0, v_declName_3753_);
v___x_3779_ = v___x_3773_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_declName_3753_);
v___x_3779_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3780_, 0, v_a_3764_);
lean_ctor_set(v___x_3780_, 1, v_a_3762_);
lean_ctor_set(v___x_3780_, 2, v_prio_3755_);
lean_ctor_set(v___x_3780_, 3, v___x_3779_);
lean_ctor_set(v___x_3780_, 4, v_a_3776_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*5, v_attrKind_3754_);
v___x_3781_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_3777_, v___x_3780_, v_attrKind_3754_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec(v___y_3767_);
return v___x_3781_;
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3773_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec(v_a_3764_);
lean_dec(v_a_3762_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
v_a_3783_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3775_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3775_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v_a_3762_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
v_a_3821_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3763_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3763_);
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
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_prio_3755_);
lean_dec(v_declName_3753_);
v_a_3829_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3761_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3761_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_3837_, lean_object* v_attrKind_3838_, lean_object* v_prio_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
uint8_t v_attrKind_boxed_3845_; lean_object* v_res_3846_; 
v_attrKind_boxed_3845_ = lean_unbox(v_attrKind_3838_);
v_res_3846_ = l_Lean_Meta_addInstance(v_declName_3837_, v_attrKind_boxed_3845_, v_prio_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_3847_, lean_object* v_constName_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3855_, lean_object* v_constName_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_3855_, v_constName_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_3863_, lean_object* v_ref_3864_, lean_object* v_constName_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3864_, v_constName_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_3872_, lean_object* v_ref_3873_, lean_object* v_constName_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_3872_, v_ref_3873_, v_constName_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v_ref_3873_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_3881_, lean_object* v_ref_3882_, lean_object* v_msg_3883_, lean_object* v_declHint_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3882_, v_msg_3883_, v_declHint_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3891_, lean_object* v_ref_3892_, lean_object* v_msg_3893_, lean_object* v_declHint_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_3891_, v_ref_3892_, v_msg_3893_, v_declHint_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v_ref_3892_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_3901_, lean_object* v_declHint_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3901_, v_declHint_3902_, v___y_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_3909_, lean_object* v_declHint_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_3909_, v_declHint_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_3917_, lean_object* v_ref_3918_, lean_object* v_msg_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3918_, v_msg_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3926_, lean_object* v_ref_3927_, lean_object* v_msg_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_3926_, v_ref_3927_, v_msg_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v_ref_3927_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_3935_, uint8_t v_s_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; lean_object* v_env_3941_; lean_object* v_nextMacroScope_3942_; lean_object* v_ngen_3943_; lean_object* v_auxDeclNGen_3944_; lean_object* v_traceState_3945_; lean_object* v_messages_3946_; lean_object* v_infoState_3947_; lean_object* v_snapshotTasks_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3977_; 
v___x_3940_ = lean_st_ref_take(v___y_3938_);
v_env_3941_ = lean_ctor_get(v___x_3940_, 0);
v_nextMacroScope_3942_ = lean_ctor_get(v___x_3940_, 1);
v_ngen_3943_ = lean_ctor_get(v___x_3940_, 2);
v_auxDeclNGen_3944_ = lean_ctor_get(v___x_3940_, 3);
v_traceState_3945_ = lean_ctor_get(v___x_3940_, 4);
v_messages_3946_ = lean_ctor_get(v___x_3940_, 6);
v_infoState_3947_ = lean_ctor_get(v___x_3940_, 7);
v_snapshotTasks_3948_ = lean_ctor_get(v___x_3940_, 8);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; 
v_unused_3978_ = lean_ctor_get(v___x_3940_, 5);
lean_dec(v_unused_3978_);
v___x_3950_ = v___x_3940_;
v_isShared_3951_ = v_isSharedCheck_3977_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_snapshotTasks_3948_);
lean_inc(v_infoState_3947_);
lean_inc(v_messages_3946_);
lean_inc(v_traceState_3945_);
lean_inc(v_auxDeclNGen_3944_);
lean_inc(v_ngen_3943_);
lean_inc(v_nextMacroScope_3942_);
lean_inc(v_env_3941_);
lean_dec(v___x_3940_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3977_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
uint8_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
v___x_3952_ = 0;
v___x_3953_ = lean_box(0);
v___x_3954_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_3941_, v_declName_3935_, v_s_3936_, v___x_3952_, v___x_3953_);
v___x_3955_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 5, v___x_3955_);
lean_ctor_set(v___x_3950_, 0, v___x_3954_);
v___x_3957_ = v___x_3950_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_nextMacroScope_3942_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_ngen_3943_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v_auxDeclNGen_3944_);
lean_ctor_set(v_reuseFailAlloc_3976_, 4, v_traceState_3945_);
lean_ctor_set(v_reuseFailAlloc_3976_, 5, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3976_, 6, v_messages_3946_);
lean_ctor_set(v_reuseFailAlloc_3976_, 7, v_infoState_3947_);
lean_ctor_set(v_reuseFailAlloc_3976_, 8, v_snapshotTasks_3948_);
v___x_3957_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v_mctx_3960_; lean_object* v_zetaDeltaFVarIds_3961_; lean_object* v_postponed_3962_; lean_object* v_diag_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3974_; 
v___x_3958_ = lean_st_ref_set(v___y_3938_, v___x_3957_);
v___x_3959_ = lean_st_ref_take(v___y_3937_);
v_mctx_3960_ = lean_ctor_get(v___x_3959_, 0);
v_zetaDeltaFVarIds_3961_ = lean_ctor_get(v___x_3959_, 2);
v_postponed_3962_ = lean_ctor_get(v___x_3959_, 3);
v_diag_3963_ = lean_ctor_get(v___x_3959_, 4);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; 
v_unused_3975_ = lean_ctor_get(v___x_3959_, 1);
lean_dec(v_unused_3975_);
v___x_3965_ = v___x_3959_;
v_isShared_3966_ = v_isSharedCheck_3974_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_diag_3963_);
lean_inc(v_postponed_3962_);
lean_inc(v_zetaDeltaFVarIds_3961_);
lean_inc(v_mctx_3960_);
lean_dec(v___x_3959_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3974_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v___x_3967_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_mctx_3960_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_zetaDeltaFVarIds_3961_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v_postponed_3962_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v_diag_3963_);
v___x_3969_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = lean_st_ref_set(v___y_3937_, v___x_3969_);
v___x_3971_ = lean_box(0);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_3979_, lean_object* v_s_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v_s_boxed_3984_; lean_object* v_res_3985_; 
v_s_boxed_3984_ = lean_unbox(v_s_3980_);
v_res_3985_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3979_, v_s_boxed_3984_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec(v___y_3981_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_3986_, uint8_t v_s_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3986_, v_s_3987_, v___y_3989_, v___y_3991_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_3994_, lean_object* v_s_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
uint8_t v_s_boxed_4001_; lean_object* v_res_4002_; 
v_s_boxed_4001_ = lean_unbox(v_s_3995_);
v_res_4002_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_3994_, v_s_boxed_4001_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4003_, uint8_t v_attrKind_4004_, lean_object* v_prio_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
uint8_t v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4011_ = 3;
lean_inc(v_declName_4003_);
v___x_4012_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4003_, v___x_4011_, v_a_4007_, v_a_4009_);
lean_dec_ref(v___x_4012_);
v___x_4013_ = l_Lean_Meta_addInstance(v_declName_4003_, v_attrKind_4004_, v_prio_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4014_, lean_object* v_attrKind_4015_, lean_object* v_prio_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
uint8_t v_attrKind_boxed_4022_; lean_object* v_res_4023_; 
v_attrKind_boxed_4022_ = lean_unbox(v_attrKind_4015_);
v_res_4023_ = l_Lean_Meta_registerInstance(v_declName_4014_, v_attrKind_boxed_4022_, v_prio_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4024_, lean_object* v_x_4025_){
_start:
{
lean_inc_ref(v_a_4024_);
return v_a_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4026_, lean_object* v_x_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4026_, v_x_4027_);
lean_dec_ref(v_x_4027_);
lean_dec_ref(v_a_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; lean_object* v_env_4034_; lean_object* v_options_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4033_ = lean_st_ref_get(v___y_4031_);
v_env_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc_ref(v_env_4034_);
lean_dec(v___x_4033_);
v_options_4035_ = lean_ctor_get(v___y_4030_, 2);
v___x_4036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_4037_ = lean_unsigned_to_nat(32u);
v___x_4038_ = lean_mk_empty_array_with_capacity(v___x_4037_);
lean_dec_ref(v___x_4038_);
v___x_4039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_4035_);
v___x_4040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4040_, 0, v_env_4034_);
lean_ctor_set(v___x_4040_, 1, v___x_4036_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
lean_ctor_set(v___x_4040_, 3, v_options_4035_);
v___x_4041_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
lean_ctor_set(v___x_4041_, 1, v_msgData_4029_);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
lean_object* v_ref_4052_; lean_object* v___x_4053_; lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4062_; 
v_ref_4052_ = lean_ctor_get(v___y_4049_, 5);
v___x_4053_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4048_, v___y_4049_, v___y_4050_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4062_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4062_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
lean_inc(v_ref_4052_);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v_ref_4052_);
lean_ctor_set(v___x_4058_, 1, v_a_4054_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set_tag(v___x_4056_, 1);
lean_ctor_set(v___x_4056_, 0, v___x_4058_);
v___x_4060_ = v___x_4056_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
return v_res_4067_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4068_, lean_object* v_i_4069_, lean_object* v_k_4070_){
_start:
{
lean_object* v___x_4071_; uint8_t v___x_4072_; 
v___x_4071_ = lean_array_get_size(v_keys_4068_);
v___x_4072_ = lean_nat_dec_lt(v_i_4069_, v___x_4071_);
if (v___x_4072_ == 0)
{
lean_dec(v_i_4069_);
return v___x_4072_;
}
else
{
lean_object* v_k_x27_4073_; uint8_t v___x_4074_; 
v_k_x27_4073_ = lean_array_fget_borrowed(v_keys_4068_, v_i_4069_);
v___x_4074_ = lean_name_eq(v_k_4070_, v_k_x27_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_unsigned_to_nat(1u);
v___x_4076_ = lean_nat_add(v_i_4069_, v___x_4075_);
lean_dec(v_i_4069_);
v_i_4069_ = v___x_4076_;
goto _start;
}
else
{
lean_dec(v_i_4069_);
return v___x_4074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4078_, lean_object* v_i_4079_, lean_object* v_k_4080_){
_start:
{
uint8_t v_res_4081_; lean_object* v_r_4082_; 
v_res_4081_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4078_, v_i_4079_, v_k_4080_);
lean_dec(v_k_4080_);
lean_dec_ref(v_keys_4078_);
v_r_4082_ = lean_box(v_res_4081_);
return v_r_4082_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4083_, size_t v_x_4084_, lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4083_) == 0)
{
lean_object* v_es_4086_; lean_object* v___x_4087_; size_t v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; lean_object* v_j_4091_; lean_object* v___x_4092_; 
v_es_4086_ = lean_ctor_get(v_x_4083_, 0);
lean_inc_ref(v_es_4086_);
lean_dec_ref(v_x_4083_);
v___x_4087_ = lean_box(2);
v___x_4088_ = ((size_t)5ULL);
v___x_4089_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4090_ = lean_usize_land(v_x_4084_, v___x_4089_);
v_j_4091_ = lean_usize_to_nat(v___x_4090_);
v___x_4092_ = lean_array_get(v___x_4087_, v_es_4086_, v_j_4091_);
lean_dec(v_j_4091_);
lean_dec_ref(v_es_4086_);
switch(lean_obj_tag(v___x_4092_))
{
case 0:
{
lean_object* v_key_4093_; uint8_t v___x_4094_; 
v_key_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_key_4093_);
lean_dec_ref(v___x_4092_);
v___x_4094_ = lean_name_eq(v_x_4085_, v_key_4093_);
lean_dec(v_key_4093_);
return v___x_4094_;
}
case 1:
{
lean_object* v_node_4095_; size_t v___x_4096_; 
v_node_4095_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_node_4095_);
lean_dec_ref(v___x_4092_);
v___x_4096_ = lean_usize_shift_right(v_x_4084_, v___x_4088_);
v_x_4083_ = v_node_4095_;
v_x_4084_ = v___x_4096_;
goto _start;
}
default: 
{
uint8_t v___x_4098_; 
v___x_4098_ = 0;
return v___x_4098_;
}
}
}
else
{
lean_object* v_ks_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v_ks_4099_ = lean_ctor_get(v_x_4083_, 0);
lean_inc_ref(v_ks_4099_);
lean_dec_ref(v_x_4083_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4099_, v___x_4100_, v_x_4085_);
lean_dec_ref(v_ks_4099_);
return v___x_4101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4102_, lean_object* v_x_4103_, lean_object* v_x_4104_){
_start:
{
size_t v_x_2499__boxed_4105_; uint8_t v_res_4106_; lean_object* v_r_4107_; 
v_x_2499__boxed_4105_ = lean_unbox_usize(v_x_4103_);
lean_dec(v_x_4103_);
v_res_4106_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4102_, v_x_2499__boxed_4105_, v_x_4104_);
lean_dec(v_x_4104_);
v_r_4107_ = lean_box(v_res_4106_);
return v_r_4107_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4108_, lean_object* v_x_4109_){
_start:
{
uint64_t v___y_4111_; 
if (lean_obj_tag(v_x_4109_) == 0)
{
uint64_t v___x_4114_; 
v___x_4114_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4111_ = v___x_4114_;
goto v___jp_4110_;
}
else
{
uint64_t v_hash_4115_; 
v_hash_4115_ = lean_ctor_get_uint64(v_x_4109_, sizeof(void*)*2);
v___y_4111_ = v_hash_4115_;
goto v___jp_4110_;
}
v___jp_4110_:
{
size_t v___x_4112_; uint8_t v___x_4113_; 
v___x_4112_ = lean_uint64_to_usize(v___y_4111_);
v___x_4113_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4108_, v___x_4112_, v_x_4109_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4116_, lean_object* v_x_4117_){
_start:
{
uint8_t v_res_4118_; lean_object* v_r_4119_; 
v_res_4118_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4116_, v_x_4117_);
lean_dec(v_x_4117_);
v_r_4119_ = lean_box(v_res_4118_);
return v_r_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4120_, lean_object* v_declName_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_instanceNames_4128_; uint8_t v___x_4129_; 
v_instanceNames_4128_ = lean_ctor_get(v_d_4120_, 1);
lean_inc_ref(v_instanceNames_4128_);
v___x_4129_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4128_, v_declName_4121_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v_d_4120_);
v___x_4130_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4131_ = l_Lean_MessageData_ofConstName(v_declName_4121_, v___x_4129_);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4134_, v___y_4122_, v___y_4123_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
else
{
goto v___jp_4125_;
}
v___jp_4125_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = l_Lean_Meta_Instances_eraseCore(v_d_4120_, v_declName_4121_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4144_, lean_object* v_declName_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4144_, v_declName_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4150_, lean_object* v_declName_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; lean_object* v_env_4156_; lean_object* v___x_4157_; lean_object* v_ext_4158_; lean_object* v_toEnvExtension_4159_; lean_object* v_asyncMode_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4155_ = lean_st_ref_get(v___y_4153_);
v_env_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc_ref(v_env_4156_);
lean_dec(v___x_4155_);
v___x_4157_ = l_Lean_Meta_instanceExtension;
v_ext_4158_ = lean_ctor_get(v___x_4157_, 1);
lean_inc_ref(v_ext_4158_);
v_toEnvExtension_4159_ = lean_ctor_get(v_ext_4158_, 0);
lean_inc_ref(v_toEnvExtension_4159_);
lean_dec_ref(v_ext_4158_);
v_asyncMode_4160_ = lean_ctor_get(v_toEnvExtension_4159_, 2);
lean_inc(v_asyncMode_4160_);
lean_dec_ref(v_toEnvExtension_4159_);
v___x_4161_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4150_, v___x_4157_, v_env_4156_, v_asyncMode_4160_);
lean_dec(v_asyncMode_4160_);
v___x_4162_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4161_, v_declName_4151_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4192_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4192_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4192_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v_env_4168_; lean_object* v_nextMacroScope_4169_; lean_object* v_ngen_4170_; lean_object* v_auxDeclNGen_4171_; lean_object* v_traceState_4172_; lean_object* v_messages_4173_; lean_object* v_infoState_4174_; lean_object* v_snapshotTasks_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4190_; 
v___x_4167_ = lean_st_ref_take(v___y_4153_);
v_env_4168_ = lean_ctor_get(v___x_4167_, 0);
v_nextMacroScope_4169_ = lean_ctor_get(v___x_4167_, 1);
v_ngen_4170_ = lean_ctor_get(v___x_4167_, 2);
v_auxDeclNGen_4171_ = lean_ctor_get(v___x_4167_, 3);
v_traceState_4172_ = lean_ctor_get(v___x_4167_, 4);
v_messages_4173_ = lean_ctor_get(v___x_4167_, 6);
v_infoState_4174_ = lean_ctor_get(v___x_4167_, 7);
v_snapshotTasks_4175_ = lean_ctor_get(v___x_4167_, 8);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v___x_4167_, 5);
lean_dec(v_unused_4191_);
v___x_4177_ = v___x_4167_;
v_isShared_4178_ = v_isSharedCheck_4190_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_snapshotTasks_4175_);
lean_inc(v_infoState_4174_);
lean_inc(v_messages_4173_);
lean_inc(v_traceState_4172_);
lean_inc(v_auxDeclNGen_4171_);
lean_inc(v_ngen_4170_);
lean_inc(v_nextMacroScope_4169_);
lean_inc(v_env_4168_);
lean_dec(v___x_4167_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4190_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___f_4179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4179_, 0, v_a_4163_);
v___x_4180_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4157_, v_env_4168_, v___f_4179_);
v___x_4181_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 5, v___x_4181_);
lean_ctor_set(v___x_4177_, 0, v___x_4180_);
v___x_4183_ = v___x_4177_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_nextMacroScope_4169_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v_ngen_4170_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v_auxDeclNGen_4171_);
lean_ctor_set(v_reuseFailAlloc_4189_, 4, v_traceState_4172_);
lean_ctor_set(v_reuseFailAlloc_4189_, 5, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4189_, 6, v_messages_4173_);
lean_ctor_set(v_reuseFailAlloc_4189_, 7, v_infoState_4174_);
lean_ctor_set(v_reuseFailAlloc_4189_, 8, v_snapshotTasks_4175_);
v___x_4183_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4184_ = lean_st_ref_set(v___y_4153_, v___x_4183_);
v___x_4185_ = lean_box(0);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4185_);
v___x_4187_ = v___x_4165_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4162_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4162_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4201_, lean_object* v_declName_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4201_, v_declName_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4211_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
lean_ctor_set(v___x_4211_, 2, v___x_4210_);
lean_ctor_set(v___x_4211_, 3, v___x_4210_);
lean_ctor_set(v___x_4211_, 4, v___x_4210_);
lean_ctor_set(v___x_4211_, 5, v___x_4210_);
return v___x_4211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
lean_ctor_set(v___x_4213_, 2, v___x_4212_);
lean_ctor_set(v___x_4213_, 3, v___x_4212_);
lean_ctor_set(v___x_4213_, 4, v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v_declName_4216_, lean_object* v_stx_4217_, uint8_t v_attrKind_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = lean_unsigned_to_nat(1u);
v___x_4223_ = l_Lean_Syntax_getArg(v_stx_4217_, v___x_4222_);
lean_inc_ref(v___y_4219_);
v___x_4224_ = l_Lean_getAttrParamOptPrio(v___x_4223_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref(v___x_4224_);
v___x_4226_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_4227_ = 0;
v___x_4228_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4229_ = lean_unsigned_to_nat(32u);
v___x_4230_ = lean_mk_empty_array_with_capacity(v___x_4229_);
v___x_4231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4232_ = ((size_t)5ULL);
lean_inc_n(v___x_4214_, 2);
v___x_4233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4233_, 0, v___x_4231_);
lean_ctor_set(v___x_4233_, 1, v___x_4230_);
lean_ctor_set(v___x_4233_, 2, v___x_4214_);
lean_ctor_set(v___x_4233_, 3, v___x_4214_);
lean_ctor_set_usize(v___x_4233_, 4, v___x_4232_);
v___x_4234_ = lean_box(1);
lean_inc_ref(v___x_4233_);
v___x_4235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4228_);
lean_ctor_set(v___x_4235_, 1, v___x_4233_);
lean_ctor_set(v___x_4235_, 2, v___x_4234_);
v___x_4236_ = lean_mk_empty_array_with_capacity(v___x_4214_);
v___x_4237_ = lean_box(0);
v___x_4238_ = 1;
lean_inc(v___x_4214_);
lean_inc(v___x_4215_);
v___x_4239_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4239_, 0, v___x_4226_);
lean_ctor_set(v___x_4239_, 1, v___x_4215_);
lean_ctor_set(v___x_4239_, 2, v___x_4235_);
lean_ctor_set(v___x_4239_, 3, v___x_4236_);
lean_ctor_set(v___x_4239_, 4, v___x_4237_);
lean_ctor_set(v___x_4239_, 5, v___x_4214_);
lean_ctor_set(v___x_4239_, 6, v___x_4237_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*7, v___x_4227_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*7 + 1, v___x_4227_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*7 + 2, v___x_4227_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*7 + 3, v___x_4238_);
lean_inc_n(v___x_4214_, 2);
v___x_4240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4214_);
lean_ctor_set(v___x_4240_, 1, v___x_4214_);
lean_ctor_set(v___x_4240_, 2, v___x_4214_);
lean_ctor_set(v___x_4240_, 3, v___x_4228_);
lean_ctor_set(v___x_4240_, 4, v___x_4228_);
lean_ctor_set(v___x_4240_, 5, v___x_4228_);
lean_ctor_set(v___x_4240_, 6, v___x_4228_);
lean_ctor_set(v___x_4240_, 7, v___x_4228_);
lean_ctor_set(v___x_4240_, 8, v___x_4228_);
v___x_4241_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4242_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4240_);
lean_ctor_set(v___x_4243_, 1, v___x_4241_);
lean_ctor_set(v___x_4243_, 2, v___x_4215_);
lean_ctor_set(v___x_4243_, 3, v___x_4233_);
lean_ctor_set(v___x_4243_, 4, v___x_4242_);
v___x_4244_ = lean_st_mk_ref(v___x_4243_);
lean_inc(v___x_4244_);
v___x_4245_ = l_Lean_Meta_addInstance(v_declName_4216_, v_attrKind_4218_, v_a_4225_, v___x_4239_, v___x_4244_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4254_; 
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; 
v_unused_4255_ = lean_ctor_get(v___x_4245_, 0);
lean_dec(v_unused_4255_);
v___x_4247_ = v___x_4245_;
v_isShared_4248_ = v_isSharedCheck_4254_;
goto v_resetjp_4246_;
}
else
{
lean_dec(v___x_4245_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4254_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4249_ = lean_st_ref_get(v___x_4244_);
lean_dec(v___x_4244_);
lean_dec(v___x_4249_);
v___x_4250_ = lean_box(0);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4250_);
v___x_4252_ = v___x_4247_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
else
{
lean_dec(v___x_4244_);
return v___x_4245_;
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v_declName_4216_);
lean_dec(v___x_4215_);
lean_dec(v___x_4214_);
v_a_4256_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4224_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4224_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v_declName_4266_, lean_object* v_stx_4267_, lean_object* v_attrKind_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
uint8_t v_attrKind_boxed_4272_; lean_object* v_res_4273_; 
v_attrKind_boxed_4272_ = lean_unbox(v_attrKind_4268_);
v_res_4273_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4264_, v___x_4265_, v_declName_4266_, v_stx_4267_, v_attrKind_boxed_4272_, v___y_4269_, v___y_4270_);
lean_dec(v_stx_4267_);
return v_res_4273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4274_; lean_object* v___f_4275_; 
v___x_4274_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4275_, 0, v___x_4274_);
return v___f_4275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4342_; lean_object* v___f_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___f_4342_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4343_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4344_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v___f_4343_);
lean_ctor_set(v___x_4345_, 2, v___f_4342_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4348_ = l_Lean_registerBuiltinAttribute(v___x_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4351_, lean_object* v_x_4352_, lean_object* v_x_4353_){
_start:
{
uint8_t v___x_4354_; 
v___x_4354_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4352_, v_x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4355_, lean_object* v_x_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_res_4358_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4355_, v_x_4356_, v_x_4357_);
lean_dec(v_x_4357_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4360_, lean_object* v_msg_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4361_, v___y_4362_, v___y_4363_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_msg_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4366_, v_msg_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4372_, lean_object* v_x_4373_, size_t v_x_4374_, lean_object* v_x_4375_){
_start:
{
uint8_t v___x_4376_; 
v___x_4376_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4373_, v_x_4374_, v_x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4377_, lean_object* v_x_4378_, lean_object* v_x_4379_, lean_object* v_x_4380_){
_start:
{
size_t v_x_3090__boxed_4381_; uint8_t v_res_4382_; lean_object* v_r_4383_; 
v_x_3090__boxed_4381_ = lean_unbox_usize(v_x_4379_);
lean_dec(v_x_4379_);
v_res_4382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4377_, v_x_4378_, v_x_3090__boxed_4381_, v_x_4380_);
lean_dec(v_x_4380_);
v_r_4383_ = lean_box(v_res_4382_);
return v_r_4383_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4384_, lean_object* v_keys_4385_, lean_object* v_vals_4386_, lean_object* v_heq_4387_, lean_object* v_i_4388_, lean_object* v_k_4389_){
_start:
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4385_, v_i_4388_, v_k_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4391_, lean_object* v_keys_4392_, lean_object* v_vals_4393_, lean_object* v_heq_4394_, lean_object* v_i_4395_, lean_object* v_k_4396_){
_start:
{
uint8_t v_res_4397_; lean_object* v_r_4398_; 
v_res_4397_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4391_, v_keys_4392_, v_vals_4393_, v_heq_4394_, v_i_4395_, v_k_4396_);
lean_dec(v_k_4396_);
lean_dec_ref(v_vals_4393_);
lean_dec_ref(v_keys_4392_);
v_r_4398_ = lean_box(v_res_4397_);
return v_r_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4401_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4402_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4403_ = l_Lean_addBuiltinDocString(v___x_4401_, v___x_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4406_){
_start:
{
lean_object* v___x_4408_; lean_object* v_env_4409_; lean_object* v___x_4410_; lean_object* v_ext_4411_; lean_object* v_toEnvExtension_4412_; lean_object* v_asyncMode_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v_discrTree_4416_; lean_object* v___x_4417_; 
v___x_4408_ = lean_st_ref_get(v_a_4406_);
v_env_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc_ref(v_env_4409_);
lean_dec(v___x_4408_);
v___x_4410_ = l_Lean_Meta_instanceExtension;
v_ext_4411_ = lean_ctor_get(v___x_4410_, 1);
lean_inc_ref(v_ext_4411_);
v_toEnvExtension_4412_ = lean_ctor_get(v_ext_4411_, 0);
lean_inc_ref(v_toEnvExtension_4412_);
lean_dec_ref(v_ext_4411_);
v_asyncMode_4413_ = lean_ctor_get(v_toEnvExtension_4412_, 2);
lean_inc(v_asyncMode_4413_);
lean_dec_ref(v_toEnvExtension_4412_);
v___x_4414_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4415_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4414_, v___x_4410_, v_env_4409_, v_asyncMode_4413_);
lean_dec(v_asyncMode_4413_);
v_discrTree_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc_ref(v_discrTree_4416_);
lean_dec(v___x_4415_);
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v_discrTree_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4418_);
lean_dec(v_a_4418_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4422_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4425_, v_a_4426_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; lean_object* v_env_4432_; lean_object* v___x_4433_; lean_object* v_ext_4434_; lean_object* v_toEnvExtension_4435_; lean_object* v_asyncMode_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v_erased_4439_; lean_object* v___x_4440_; 
v___x_4431_ = lean_st_ref_get(v_a_4429_);
v_env_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc_ref(v_env_4432_);
lean_dec(v___x_4431_);
v___x_4433_ = l_Lean_Meta_instanceExtension;
v_ext_4434_ = lean_ctor_get(v___x_4433_, 1);
lean_inc_ref(v_ext_4434_);
v_toEnvExtension_4435_ = lean_ctor_get(v_ext_4434_, 0);
lean_inc_ref(v_toEnvExtension_4435_);
lean_dec_ref(v_ext_4434_);
v_asyncMode_4436_ = lean_ctor_get(v_toEnvExtension_4435_, 2);
lean_inc(v_asyncMode_4436_);
lean_dec_ref(v_toEnvExtension_4435_);
v___x_4437_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4438_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4437_, v___x_4433_, v_env_4432_, v_asyncMode_4436_);
lean_dec(v_asyncMode_4436_);
v_erased_4439_ = lean_ctor_get(v___x_4438_, 2);
lean_inc_ref(v_erased_4439_);
lean_dec(v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v_erased_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4441_);
lean_dec(v_a_4441_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4445_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Meta_getErasedInstances(v_a_4448_, v_a_4449_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
return v_res_4451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4452_, lean_object* v_declName_4453_){
_start:
{
lean_object* v___x_4454_; lean_object* v_ext_4455_; lean_object* v_toEnvExtension_4456_; lean_object* v_asyncMode_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_instanceNames_4460_; uint8_t v___x_4461_; 
v___x_4454_ = l_Lean_Meta_instanceExtension;
v_ext_4455_ = lean_ctor_get(v___x_4454_, 1);
lean_inc_ref(v_ext_4455_);
v_toEnvExtension_4456_ = lean_ctor_get(v_ext_4455_, 0);
lean_inc_ref(v_toEnvExtension_4456_);
lean_dec_ref(v_ext_4455_);
v_asyncMode_4457_ = lean_ctor_get(v_toEnvExtension_4456_, 2);
lean_inc(v_asyncMode_4457_);
lean_dec_ref(v_toEnvExtension_4456_);
v___x_4458_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4459_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4458_, v___x_4454_, v_env_4452_, v_asyncMode_4457_);
lean_dec(v_asyncMode_4457_);
v_instanceNames_4460_ = lean_ctor_get(v___x_4459_, 1);
lean_inc_ref(v_instanceNames_4460_);
lean_dec(v___x_4459_);
v___x_4461_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4460_, v_declName_4453_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4462_, lean_object* v_declName_4463_){
_start:
{
uint8_t v_res_4464_; lean_object* v_r_4465_; 
v_res_4464_ = l_Lean_Meta_isInstanceCore(v_env_4462_, v_declName_4463_);
lean_dec(v_declName_4463_);
v_r_4465_ = lean_box(v_res_4464_);
return v_r_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v_env_4470_; uint8_t v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4469_ = lean_st_ref_get(v_a_4467_);
v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc_ref(v_env_4470_);
lean_dec(v___x_4469_);
v___x_4471_ = l_Lean_Meta_isInstanceCore(v_env_4470_, v_declName_4466_);
v___x_4472_ = lean_box(v___x_4471_);
v___x_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_Meta_isInstance___redArg(v_declName_4474_, v_a_4475_);
lean_dec(v_a_4475_);
lean_dec(v_declName_4474_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Meta_isInstance___redArg(v_declName_4478_, v_a_4480_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_Meta_isInstance(v_declName_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_declName_4483_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4488_, lean_object* v_vals_4489_, lean_object* v_i_4490_, lean_object* v_k_4491_){
_start:
{
lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4492_ = lean_array_get_size(v_keys_4488_);
v___x_4493_ = lean_nat_dec_lt(v_i_4490_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
lean_dec(v_i_4490_);
v___x_4494_ = lean_box(0);
return v___x_4494_;
}
else
{
lean_object* v_k_x27_4495_; uint8_t v___x_4496_; 
v_k_x27_4495_ = lean_array_fget_borrowed(v_keys_4488_, v_i_4490_);
v___x_4496_ = lean_name_eq(v_k_4491_, v_k_x27_4495_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = lean_unsigned_to_nat(1u);
v___x_4498_ = lean_nat_add(v_i_4490_, v___x_4497_);
lean_dec(v_i_4490_);
v_i_4490_ = v___x_4498_;
goto _start;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_array_fget_borrowed(v_vals_4489_, v_i_4490_);
lean_dec(v_i_4490_);
lean_inc(v___x_4500_);
v___x_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4502_, lean_object* v_vals_4503_, lean_object* v_i_4504_, lean_object* v_k_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4502_, v_vals_4503_, v_i_4504_, v_k_4505_);
lean_dec(v_k_4505_);
lean_dec_ref(v_vals_4503_);
lean_dec_ref(v_keys_4502_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4507_, size_t v_x_4508_, lean_object* v_x_4509_){
_start:
{
if (lean_obj_tag(v_x_4507_) == 0)
{
lean_object* v_es_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4531_; 
v_es_4510_ = lean_ctor_get(v_x_4507_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_x_4507_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4512_ = v_x_4507_;
v_isShared_4513_ = v_isSharedCheck_4531_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_es_4510_);
lean_dec(v_x_4507_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4531_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4514_; size_t v___x_4515_; size_t v___x_4516_; size_t v___x_4517_; lean_object* v_j_4518_; lean_object* v___x_4519_; 
v___x_4514_ = lean_box(2);
v___x_4515_ = ((size_t)5ULL);
v___x_4516_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4517_ = lean_usize_land(v_x_4508_, v___x_4516_);
v_j_4518_ = lean_usize_to_nat(v___x_4517_);
v___x_4519_ = lean_array_get(v___x_4514_, v_es_4510_, v_j_4518_);
lean_dec(v_j_4518_);
lean_dec_ref(v_es_4510_);
switch(lean_obj_tag(v___x_4519_))
{
case 0:
{
lean_object* v_key_4520_; lean_object* v_val_4521_; uint8_t v___x_4522_; 
v_key_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_key_4520_);
v_val_4521_ = lean_ctor_get(v___x_4519_, 1);
lean_inc(v_val_4521_);
lean_dec_ref(v___x_4519_);
v___x_4522_ = lean_name_eq(v_x_4509_, v_key_4520_);
lean_dec(v_key_4520_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; 
lean_dec(v_val_4521_);
lean_del_object(v___x_4512_);
v___x_4523_ = lean_box(0);
return v___x_4523_;
}
else
{
lean_object* v___x_4525_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set_tag(v___x_4512_, 1);
lean_ctor_set(v___x_4512_, 0, v_val_4521_);
v___x_4525_ = v___x_4512_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_val_4521_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
case 1:
{
lean_object* v_node_4527_; size_t v___x_4528_; 
lean_del_object(v___x_4512_);
v_node_4527_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_node_4527_);
lean_dec_ref(v___x_4519_);
v___x_4528_ = lean_usize_shift_right(v_x_4508_, v___x_4515_);
v_x_4507_ = v_node_4527_;
v_x_4508_ = v___x_4528_;
goto _start;
}
default: 
{
lean_object* v___x_4530_; 
lean_del_object(v___x_4512_);
v___x_4530_ = lean_box(0);
return v___x_4530_;
}
}
}
}
else
{
lean_object* v_ks_4532_; lean_object* v_vs_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_ks_4532_ = lean_ctor_get(v_x_4507_, 0);
lean_inc_ref(v_ks_4532_);
v_vs_4533_ = lean_ctor_get(v_x_4507_, 1);
lean_inc_ref(v_vs_4533_);
lean_dec_ref(v_x_4507_);
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4532_, v_vs_4533_, v___x_4534_, v_x_4509_);
lean_dec_ref(v_vs_4533_);
lean_dec_ref(v_ks_4532_);
return v___x_4535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4536_, lean_object* v_x_4537_, lean_object* v_x_4538_){
_start:
{
size_t v_x_713__boxed_4539_; lean_object* v_res_4540_; 
v_x_713__boxed_4539_ = lean_unbox_usize(v_x_4537_);
lean_dec(v_x_4537_);
v_res_4540_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4536_, v_x_713__boxed_4539_, v_x_4538_);
lean_dec(v_x_4538_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4541_, lean_object* v_x_4542_){
_start:
{
uint64_t v___y_4544_; 
if (lean_obj_tag(v_x_4542_) == 0)
{
uint64_t v___x_4547_; 
v___x_4547_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4544_ = v___x_4547_;
goto v___jp_4543_;
}
else
{
uint64_t v_hash_4548_; 
v_hash_4548_ = lean_ctor_get_uint64(v_x_4542_, sizeof(void*)*2);
v___y_4544_ = v_hash_4548_;
goto v___jp_4543_;
}
v___jp_4543_:
{
size_t v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_uint64_to_usize(v___y_4544_);
v___x_4546_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4541_, v___x_4545_, v_x_4542_);
return v___x_4546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4549_, lean_object* v_x_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4549_, v_x_4550_);
lean_dec(v_x_4550_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v___x_4555_; lean_object* v_env_4556_; lean_object* v___x_4557_; lean_object* v_ext_4558_; lean_object* v_toEnvExtension_4559_; lean_object* v_asyncMode_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v_instanceNames_4563_; lean_object* v___x_4564_; 
v___x_4555_ = lean_st_ref_get(v_a_4553_);
v_env_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc_ref(v_env_4556_);
lean_dec(v___x_4555_);
v___x_4557_ = l_Lean_Meta_instanceExtension;
v_ext_4558_ = lean_ctor_get(v___x_4557_, 1);
lean_inc_ref(v_ext_4558_);
v_toEnvExtension_4559_ = lean_ctor_get(v_ext_4558_, 0);
lean_inc_ref(v_toEnvExtension_4559_);
lean_dec_ref(v_ext_4558_);
v_asyncMode_4560_ = lean_ctor_get(v_toEnvExtension_4559_, 2);
lean_inc(v_asyncMode_4560_);
lean_dec_ref(v_toEnvExtension_4559_);
v___x_4561_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4562_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4561_, v___x_4557_, v_env_4556_, v_asyncMode_4560_);
lean_dec(v_asyncMode_4560_);
v_instanceNames_4563_ = lean_ctor_get(v___x_4562_, 1);
lean_inc_ref(v_instanceNames_4563_);
lean_dec(v___x_4562_);
v___x_4564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4563_, v_declName_4552_);
if (lean_obj_tag(v___x_4564_) == 1)
{
lean_object* v_val_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4574_; 
v_val_4565_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4567_ = v___x_4564_;
v_isShared_4568_ = v_isSharedCheck_4574_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_val_4565_);
lean_dec(v___x_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4574_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v_priority_4569_; lean_object* v___x_4571_; 
v_priority_4569_ = lean_ctor_get(v_val_4565_, 2);
lean_inc(v_priority_4569_);
lean_dec(v_val_4565_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v_priority_4569_);
v___x_4571_ = v___x_4567_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_priority_4569_);
v___x_4571_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
}
else
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
lean_dec(v___x_4564_);
v___x_4575_ = lean_box(0);
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
return v___x_4576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec(v_declName_4577_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4581_, v_a_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_declName_4586_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4591_, lean_object* v_x_4592_, lean_object* v_x_4593_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4592_, v_x_4593_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4595_, lean_object* v_x_4596_, lean_object* v_x_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4595_, v_x_4596_, v_x_4597_);
lean_dec(v_x_4597_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4599_, lean_object* v_x_4600_, size_t v_x_4601_, lean_object* v_x_4602_){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4600_, v_x_4601_, v_x_4602_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4604_, lean_object* v_x_4605_, lean_object* v_x_4606_, lean_object* v_x_4607_){
_start:
{
size_t v_x_850__boxed_4608_; lean_object* v_res_4609_; 
v_x_850__boxed_4608_ = lean_unbox_usize(v_x_4606_);
lean_dec(v_x_4606_);
v_res_4609_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4604_, v_x_4605_, v_x_850__boxed_4608_, v_x_4607_);
lean_dec(v_x_4607_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4610_, lean_object* v_keys_4611_, lean_object* v_vals_4612_, lean_object* v_heq_4613_, lean_object* v_i_4614_, lean_object* v_k_4615_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4611_, v_vals_4612_, v_i_4614_, v_k_4615_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4617_, lean_object* v_keys_4618_, lean_object* v_vals_4619_, lean_object* v_heq_4620_, lean_object* v_i_4621_, lean_object* v_k_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4617_, v_keys_4618_, v_vals_4619_, v_heq_4620_, v_i_4621_, v_k_4622_);
lean_dec(v_k_4622_);
lean_dec_ref(v_vals_4619_);
lean_dec_ref(v_keys_4618_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v___x_4627_; lean_object* v_env_4628_; lean_object* v___x_4629_; lean_object* v_ext_4630_; lean_object* v_toEnvExtension_4631_; lean_object* v_asyncMode_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v_instanceNames_4635_; lean_object* v___x_4636_; 
v___x_4627_ = lean_st_ref_get(v_a_4625_);
v_env_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc_ref(v_env_4628_);
lean_dec(v___x_4627_);
v___x_4629_ = l_Lean_Meta_instanceExtension;
v_ext_4630_ = lean_ctor_get(v___x_4629_, 1);
lean_inc_ref(v_ext_4630_);
v_toEnvExtension_4631_ = lean_ctor_get(v_ext_4630_, 0);
lean_inc_ref(v_toEnvExtension_4631_);
lean_dec_ref(v_ext_4630_);
v_asyncMode_4632_ = lean_ctor_get(v_toEnvExtension_4631_, 2);
lean_inc(v_asyncMode_4632_);
lean_dec_ref(v_toEnvExtension_4631_);
v___x_4633_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4634_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4633_, v___x_4629_, v_env_4628_, v_asyncMode_4632_);
lean_dec(v_asyncMode_4632_);
v_instanceNames_4635_ = lean_ctor_get(v___x_4634_, 1);
lean_inc_ref(v_instanceNames_4635_);
lean_dec(v___x_4634_);
v___x_4636_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4635_, v_declName_4624_);
if (lean_obj_tag(v___x_4636_) == 1)
{
lean_object* v_val_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4647_; 
v_val_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4647_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_val_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4647_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
uint8_t v_attrKind_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
v_attrKind_4641_ = lean_ctor_get_uint8(v_val_4637_, sizeof(void*)*5);
lean_dec(v_val_4637_);
v___x_4642_ = lean_box(v_attrKind_4641_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4642_);
v___x_4644_ = v___x_4639_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
}
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec(v___x_4636_);
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec(v_declName_4650_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4654_, v_a_4656_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4659_, v_a_4660_, v_a_4661_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_declName_4659_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_4668_, lean_object* v_v_4669_, lean_object* v_t_4670_){
_start:
{
if (lean_obj_tag(v_t_4670_) == 0)
{
lean_object* v_size_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v_l_4674_; lean_object* v_r_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4956_; 
v_size_4671_ = lean_ctor_get(v_t_4670_, 0);
v_k_4672_ = lean_ctor_get(v_t_4670_, 1);
v_v_4673_ = lean_ctor_get(v_t_4670_, 2);
v_l_4674_ = lean_ctor_get(v_t_4670_, 3);
v_r_4675_ = lean_ctor_get(v_t_4670_, 4);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_t_4670_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4677_ = v_t_4670_;
v_isShared_4678_ = v_isSharedCheck_4956_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_r_4675_);
lean_inc(v_l_4674_);
lean_inc(v_v_4673_);
lean_inc(v_k_4672_);
lean_inc(v_size_4671_);
lean_dec(v_t_4670_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4956_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
uint8_t v___x_4679_; 
v___x_4679_ = lean_nat_dec_lt(v_k_4672_, v_k_4668_);
if (v___x_4679_ == 0)
{
uint8_t v___x_4680_; 
v___x_4680_ = lean_nat_dec_eq(v_k_4672_, v_k_4668_);
if (v___x_4680_ == 0)
{
lean_object* v_impl_4681_; lean_object* v___x_4682_; 
lean_dec(v_size_4671_);
v_impl_4681_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4668_, v_v_4669_, v_r_4675_);
v___x_4682_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4674_) == 0)
{
lean_object* v_size_4683_; lean_object* v_size_4684_; lean_object* v_k_4685_; lean_object* v_v_4686_; lean_object* v_l_4687_; lean_object* v_r_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; uint8_t v___x_4691_; 
v_size_4683_ = lean_ctor_get(v_l_4674_, 0);
v_size_4684_ = lean_ctor_get(v_impl_4681_, 0);
lean_inc(v_size_4684_);
v_k_4685_ = lean_ctor_get(v_impl_4681_, 1);
lean_inc(v_k_4685_);
v_v_4686_ = lean_ctor_get(v_impl_4681_, 2);
lean_inc(v_v_4686_);
v_l_4687_ = lean_ctor_get(v_impl_4681_, 3);
lean_inc(v_l_4687_);
v_r_4688_ = lean_ctor_get(v_impl_4681_, 4);
lean_inc(v_r_4688_);
v___x_4689_ = lean_unsigned_to_nat(3u);
v___x_4690_ = lean_nat_mul(v___x_4689_, v_size_4683_);
v___x_4691_ = lean_nat_dec_lt(v___x_4690_, v_size_4684_);
lean_dec(v___x_4690_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
lean_dec(v_r_4688_);
lean_dec(v_l_4687_);
lean_dec(v_v_4686_);
lean_dec(v_k_4685_);
v___x_4692_ = lean_nat_add(v___x_4682_, v_size_4683_);
v___x_4693_ = lean_nat_add(v___x_4692_, v_size_4684_);
lean_dec(v_size_4684_);
lean_dec(v___x_4692_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_impl_4681_);
lean_ctor_set(v___x_4677_, 0, v___x_4693_);
v___x_4695_ = v___x_4677_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4696_, 4, v_impl_4681_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
else
{
lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4760_; 
v_isSharedCheck_4760_ = !lean_is_exclusive(v_impl_4681_);
if (v_isSharedCheck_4760_ == 0)
{
lean_object* v_unused_4761_; lean_object* v_unused_4762_; lean_object* v_unused_4763_; lean_object* v_unused_4764_; lean_object* v_unused_4765_; 
v_unused_4761_ = lean_ctor_get(v_impl_4681_, 4);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v_impl_4681_, 3);
lean_dec(v_unused_4762_);
v_unused_4763_ = lean_ctor_get(v_impl_4681_, 2);
lean_dec(v_unused_4763_);
v_unused_4764_ = lean_ctor_get(v_impl_4681_, 1);
lean_dec(v_unused_4764_);
v_unused_4765_ = lean_ctor_get(v_impl_4681_, 0);
lean_dec(v_unused_4765_);
v___x_4698_ = v_impl_4681_;
v_isShared_4699_ = v_isSharedCheck_4760_;
goto v_resetjp_4697_;
}
else
{
lean_dec(v_impl_4681_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4760_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_size_4700_; lean_object* v_k_4701_; lean_object* v_v_4702_; lean_object* v_l_4703_; lean_object* v_r_4704_; lean_object* v_size_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v_size_4700_ = lean_ctor_get(v_l_4687_, 0);
v_k_4701_ = lean_ctor_get(v_l_4687_, 1);
v_v_4702_ = lean_ctor_get(v_l_4687_, 2);
v_l_4703_ = lean_ctor_get(v_l_4687_, 3);
v_r_4704_ = lean_ctor_get(v_l_4687_, 4);
v_size_4705_ = lean_ctor_get(v_r_4688_, 0);
v___x_4706_ = lean_unsigned_to_nat(2u);
v___x_4707_ = lean_nat_mul(v___x_4706_, v_size_4705_);
v___x_4708_ = lean_nat_dec_lt(v_size_4700_, v___x_4707_);
lean_dec(v___x_4707_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4736_; 
lean_inc(v_r_4704_);
lean_inc(v_l_4703_);
lean_inc(v_v_4702_);
lean_inc(v_k_4701_);
v_isSharedCheck_4736_ = !lean_is_exclusive(v_l_4687_);
if (v_isSharedCheck_4736_ == 0)
{
lean_object* v_unused_4737_; lean_object* v_unused_4738_; lean_object* v_unused_4739_; lean_object* v_unused_4740_; lean_object* v_unused_4741_; 
v_unused_4737_ = lean_ctor_get(v_l_4687_, 4);
lean_dec(v_unused_4737_);
v_unused_4738_ = lean_ctor_get(v_l_4687_, 3);
lean_dec(v_unused_4738_);
v_unused_4739_ = lean_ctor_get(v_l_4687_, 2);
lean_dec(v_unused_4739_);
v_unused_4740_ = lean_ctor_get(v_l_4687_, 1);
lean_dec(v_unused_4740_);
v_unused_4741_ = lean_ctor_get(v_l_4687_, 0);
lean_dec(v_unused_4741_);
v___x_4710_ = v_l_4687_;
v_isShared_4711_ = v_isSharedCheck_4736_;
goto v_resetjp_4709_;
}
else
{
lean_dec(v_l_4687_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4736_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4726_; 
v___x_4712_ = lean_nat_add(v___x_4682_, v_size_4683_);
v___x_4713_ = lean_nat_add(v___x_4712_, v_size_4684_);
lean_dec(v_size_4684_);
if (lean_obj_tag(v_l_4703_) == 0)
{
lean_object* v_size_4734_; 
v_size_4734_ = lean_ctor_get(v_l_4703_, 0);
lean_inc(v_size_4734_);
v___y_4726_ = v_size_4734_;
goto v___jp_4725_;
}
else
{
lean_object* v___x_4735_; 
v___x_4735_ = lean_unsigned_to_nat(0u);
v___y_4726_ = v___x_4735_;
goto v___jp_4725_;
}
v___jp_4714_:
{
lean_object* v___x_4718_; lean_object* v___x_4720_; 
v___x_4718_ = lean_nat_add(v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec(v___y_4716_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 4, v_r_4688_);
lean_ctor_set(v___x_4710_, 3, v_r_4704_);
lean_ctor_set(v___x_4710_, 2, v_v_4686_);
lean_ctor_set(v___x_4710_, 1, v_k_4685_);
lean_ctor_set(v___x_4710_, 0, v___x_4718_);
v___x_4720_ = v___x_4710_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_k_4685_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_v_4686_);
lean_ctor_set(v_reuseFailAlloc_4724_, 3, v_r_4704_);
lean_ctor_set(v_reuseFailAlloc_4724_, 4, v_r_4688_);
v___x_4720_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4722_; 
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 4, v___x_4720_);
lean_ctor_set(v___x_4698_, 3, v___y_4715_);
lean_ctor_set(v___x_4698_, 2, v_v_4702_);
lean_ctor_set(v___x_4698_, 1, v_k_4701_);
lean_ctor_set(v___x_4698_, 0, v___x_4713_);
v___x_4722_ = v___x_4698_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4701_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4702_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v___y_4715_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v___x_4720_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
v___jp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4729_; 
v___x_4727_ = lean_nat_add(v___x_4712_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec(v___x_4712_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_l_4703_);
lean_ctor_set(v___x_4677_, 0, v___x_4727_);
v___x_4729_ = v___x_4677_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v_l_4703_);
v___x_4729_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_nat_add(v___x_4682_, v_size_4705_);
if (lean_obj_tag(v_r_4704_) == 0)
{
lean_object* v_size_4731_; 
v_size_4731_ = lean_ctor_get(v_r_4704_, 0);
lean_inc(v_size_4731_);
v___y_4715_ = v___x_4729_;
v___y_4716_ = v___x_4730_;
v___y_4717_ = v_size_4731_;
goto v___jp_4714_;
}
else
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_unsigned_to_nat(0u);
v___y_4715_ = v___x_4729_;
v___y_4716_ = v___x_4730_;
v___y_4717_ = v___x_4732_;
goto v___jp_4714_;
}
}
}
}
}
else
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
lean_del_object(v___x_4677_);
v___x_4742_ = lean_nat_add(v___x_4682_, v_size_4683_);
v___x_4743_ = lean_nat_add(v___x_4742_, v_size_4684_);
lean_dec(v_size_4684_);
v___x_4744_ = lean_nat_add(v___x_4742_, v_size_4700_);
lean_dec(v___x_4742_);
lean_inc_ref(v_l_4674_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 4, v_l_4687_);
lean_ctor_set(v___x_4698_, 3, v_l_4674_);
lean_ctor_set(v___x_4698_, 2, v_v_4673_);
lean_ctor_set(v___x_4698_, 1, v_k_4672_);
lean_ctor_set(v___x_4698_, 0, v___x_4744_);
v___x_4746_ = v___x_4698_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4759_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4759_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4759_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4759_, 4, v_l_4687_);
v___x_4746_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_isSharedCheck_4753_ = !lean_is_exclusive(v_l_4674_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; lean_object* v_unused_4755_; lean_object* v_unused_4756_; lean_object* v_unused_4757_; lean_object* v_unused_4758_; 
v_unused_4754_ = lean_ctor_get(v_l_4674_, 4);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_l_4674_, 3);
lean_dec(v_unused_4755_);
v_unused_4756_ = lean_ctor_get(v_l_4674_, 2);
lean_dec(v_unused_4756_);
v_unused_4757_ = lean_ctor_get(v_l_4674_, 1);
lean_dec(v_unused_4757_);
v_unused_4758_ = lean_ctor_get(v_l_4674_, 0);
lean_dec(v_unused_4758_);
v___x_4748_ = v_l_4674_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_dec(v_l_4674_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 4, v_r_4688_);
lean_ctor_set(v___x_4748_, 3, v___x_4746_);
lean_ctor_set(v___x_4748_, 2, v_v_4686_);
lean_ctor_set(v___x_4748_, 1, v_k_4685_);
lean_ctor_set(v___x_4748_, 0, v___x_4743_);
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4685_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4686_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v_r_4688_);
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
}
else
{
lean_object* v_l_4766_; 
v_l_4766_ = lean_ctor_get(v_impl_4681_, 3);
lean_inc(v_l_4766_);
if (lean_obj_tag(v_l_4766_) == 0)
{
lean_object* v_r_4767_; lean_object* v_k_4768_; lean_object* v_v_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4792_; 
v_r_4767_ = lean_ctor_get(v_impl_4681_, 4);
v_k_4768_ = lean_ctor_get(v_impl_4681_, 1);
v_v_4769_ = lean_ctor_get(v_impl_4681_, 2);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_impl_4681_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; lean_object* v_unused_4794_; 
v_unused_4793_ = lean_ctor_get(v_impl_4681_, 3);
lean_dec(v_unused_4793_);
v_unused_4794_ = lean_ctor_get(v_impl_4681_, 0);
lean_dec(v_unused_4794_);
v___x_4771_ = v_impl_4681_;
v_isShared_4772_ = v_isSharedCheck_4792_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_r_4767_);
lean_inc(v_v_4769_);
lean_inc(v_k_4768_);
lean_dec(v_impl_4681_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4792_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v_k_4773_; lean_object* v_v_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4788_; 
v_k_4773_ = lean_ctor_get(v_l_4766_, 1);
v_v_4774_ = lean_ctor_get(v_l_4766_, 2);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_l_4766_);
if (v_isSharedCheck_4788_ == 0)
{
lean_object* v_unused_4789_; lean_object* v_unused_4790_; lean_object* v_unused_4791_; 
v_unused_4789_ = lean_ctor_get(v_l_4766_, 4);
lean_dec(v_unused_4789_);
v_unused_4790_ = lean_ctor_get(v_l_4766_, 3);
lean_dec(v_unused_4790_);
v_unused_4791_ = lean_ctor_get(v_l_4766_, 0);
lean_dec(v_unused_4791_);
v___x_4776_ = v_l_4766_;
v_isShared_4777_ = v_isSharedCheck_4788_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_v_4774_);
lean_inc(v_k_4773_);
lean_dec(v_l_4766_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4788_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4778_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4767_, 2);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 4, v_r_4767_);
lean_ctor_set(v___x_4776_, 3, v_r_4767_);
lean_ctor_set(v___x_4776_, 2, v_v_4673_);
lean_ctor_set(v___x_4776_, 1, v_k_4672_);
lean_ctor_set(v___x_4776_, 0, v___x_4682_);
v___x_4780_ = v___x_4776_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v_r_4767_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v_r_4767_);
v___x_4780_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4782_; 
lean_inc(v_r_4767_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 3, v_r_4767_);
lean_ctor_set(v___x_4771_, 0, v___x_4682_);
v___x_4782_ = v___x_4771_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_k_4768_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_v_4769_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_r_4767_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v_r_4767_);
v___x_4782_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
lean_object* v___x_4784_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v___x_4782_);
lean_ctor_set(v___x_4677_, 3, v___x_4780_);
lean_ctor_set(v___x_4677_, 2, v_v_4774_);
lean_ctor_set(v___x_4677_, 1, v_k_4773_);
lean_ctor_set(v___x_4677_, 0, v___x_4778_);
v___x_4784_ = v___x_4677_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_k_4773_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_v_4774_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v___x_4780_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v___x_4782_);
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
}
else
{
lean_object* v_r_4795_; 
v_r_4795_ = lean_ctor_get(v_impl_4681_, 4);
lean_inc(v_r_4795_);
if (lean_obj_tag(v_r_4795_) == 0)
{
lean_object* v_k_4796_; lean_object* v_v_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4808_; 
v_k_4796_ = lean_ctor_get(v_impl_4681_, 1);
v_v_4797_ = lean_ctor_get(v_impl_4681_, 2);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_impl_4681_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; lean_object* v_unused_4810_; lean_object* v_unused_4811_; 
v_unused_4809_ = lean_ctor_get(v_impl_4681_, 4);
lean_dec(v_unused_4809_);
v_unused_4810_ = lean_ctor_get(v_impl_4681_, 3);
lean_dec(v_unused_4810_);
v_unused_4811_ = lean_ctor_get(v_impl_4681_, 0);
lean_dec(v_unused_4811_);
v___x_4799_ = v_impl_4681_;
v_isShared_4800_ = v_isSharedCheck_4808_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_v_4797_);
lean_inc(v_k_4796_);
lean_dec(v_impl_4681_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4808_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
v___x_4801_ = lean_unsigned_to_nat(3u);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 4, v_l_4766_);
lean_ctor_set(v___x_4799_, 2, v_v_4673_);
lean_ctor_set(v___x_4799_, 1, v_k_4672_);
lean_ctor_set(v___x_4799_, 0, v___x_4682_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_l_4766_);
lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_l_4766_);
v___x_4803_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4805_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_r_4795_);
lean_ctor_set(v___x_4677_, 3, v___x_4803_);
lean_ctor_set(v___x_4677_, 2, v_v_4797_);
lean_ctor_set(v___x_4677_, 1, v_k_4796_);
lean_ctor_set(v___x_4677_, 0, v___x_4801_);
v___x_4805_ = v___x_4677_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4796_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4797_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v___x_4803_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_r_4795_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4812_ = lean_unsigned_to_nat(2u);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_impl_4681_);
lean_ctor_set(v___x_4677_, 3, v_r_4795_);
lean_ctor_set(v___x_4677_, 0, v___x_4812_);
v___x_4814_ = v___x_4677_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_r_4795_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_impl_4681_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
}
else
{
lean_object* v___x_4817_; 
lean_dec(v_v_4673_);
lean_dec(v_k_4672_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 2, v_v_4669_);
lean_ctor_set(v___x_4677_, 1, v_k_4668_);
v___x_4817_ = v___x_4677_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_size_4671_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v_k_4668_);
lean_ctor_set(v_reuseFailAlloc_4818_, 2, v_v_4669_);
lean_ctor_set(v_reuseFailAlloc_4818_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4818_, 4, v_r_4675_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
else
{
lean_object* v_impl_4819_; lean_object* v___x_4820_; 
lean_dec(v_size_4671_);
v_impl_4819_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4668_, v_v_4669_, v_l_4674_);
v___x_4820_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4675_) == 0)
{
lean_object* v_size_4821_; lean_object* v_size_4822_; lean_object* v_k_4823_; lean_object* v_v_4824_; lean_object* v_l_4825_; lean_object* v_r_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v_size_4821_ = lean_ctor_get(v_r_4675_, 0);
v_size_4822_ = lean_ctor_get(v_impl_4819_, 0);
lean_inc(v_size_4822_);
v_k_4823_ = lean_ctor_get(v_impl_4819_, 1);
lean_inc(v_k_4823_);
v_v_4824_ = lean_ctor_get(v_impl_4819_, 2);
lean_inc(v_v_4824_);
v_l_4825_ = lean_ctor_get(v_impl_4819_, 3);
lean_inc(v_l_4825_);
v_r_4826_ = lean_ctor_get(v_impl_4819_, 4);
lean_inc(v_r_4826_);
v___x_4827_ = lean_unsigned_to_nat(3u);
v___x_4828_ = lean_nat_mul(v___x_4827_, v_size_4821_);
v___x_4829_ = lean_nat_dec_lt(v___x_4828_, v_size_4822_);
lean_dec(v___x_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4833_; 
lean_dec(v_r_4826_);
lean_dec(v_l_4825_);
lean_dec(v_v_4824_);
lean_dec(v_k_4823_);
v___x_4830_ = lean_nat_add(v___x_4820_, v_size_4822_);
lean_dec(v_size_4822_);
v___x_4831_ = lean_nat_add(v___x_4830_, v_size_4821_);
lean_dec(v___x_4830_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 3, v_impl_4819_);
lean_ctor_set(v___x_4677_, 0, v___x_4831_);
v___x_4833_ = v___x_4677_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4831_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v_impl_4819_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_r_4675_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
else
{
lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4900_; 
v_isSharedCheck_4900_ = !lean_is_exclusive(v_impl_4819_);
if (v_isSharedCheck_4900_ == 0)
{
lean_object* v_unused_4901_; lean_object* v_unused_4902_; lean_object* v_unused_4903_; lean_object* v_unused_4904_; lean_object* v_unused_4905_; 
v_unused_4901_ = lean_ctor_get(v_impl_4819_, 4);
lean_dec(v_unused_4901_);
v_unused_4902_ = lean_ctor_get(v_impl_4819_, 3);
lean_dec(v_unused_4902_);
v_unused_4903_ = lean_ctor_get(v_impl_4819_, 2);
lean_dec(v_unused_4903_);
v_unused_4904_ = lean_ctor_get(v_impl_4819_, 1);
lean_dec(v_unused_4904_);
v_unused_4905_ = lean_ctor_get(v_impl_4819_, 0);
lean_dec(v_unused_4905_);
v___x_4836_ = v_impl_4819_;
v_isShared_4837_ = v_isSharedCheck_4900_;
goto v_resetjp_4835_;
}
else
{
lean_dec(v_impl_4819_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4900_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v_size_4838_; lean_object* v_size_4839_; lean_object* v_k_4840_; lean_object* v_v_4841_; lean_object* v_l_4842_; lean_object* v_r_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v_size_4838_ = lean_ctor_get(v_l_4825_, 0);
v_size_4839_ = lean_ctor_get(v_r_4826_, 0);
v_k_4840_ = lean_ctor_get(v_r_4826_, 1);
v_v_4841_ = lean_ctor_get(v_r_4826_, 2);
v_l_4842_ = lean_ctor_get(v_r_4826_, 3);
v_r_4843_ = lean_ctor_get(v_r_4826_, 4);
v___x_4844_ = lean_unsigned_to_nat(2u);
v___x_4845_ = lean_nat_mul(v___x_4844_, v_size_4838_);
v___x_4846_ = lean_nat_dec_lt(v_size_4839_, v___x_4845_);
lean_dec(v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4875_; 
lean_inc(v_r_4843_);
lean_inc(v_l_4842_);
lean_inc(v_v_4841_);
lean_inc(v_k_4840_);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_r_4826_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; lean_object* v_unused_4877_; lean_object* v_unused_4878_; lean_object* v_unused_4879_; lean_object* v_unused_4880_; 
v_unused_4876_ = lean_ctor_get(v_r_4826_, 4);
lean_dec(v_unused_4876_);
v_unused_4877_ = lean_ctor_get(v_r_4826_, 3);
lean_dec(v_unused_4877_);
v_unused_4878_ = lean_ctor_get(v_r_4826_, 2);
lean_dec(v_unused_4878_);
v_unused_4879_ = lean_ctor_get(v_r_4826_, 1);
lean_dec(v_unused_4879_);
v_unused_4880_ = lean_ctor_get(v_r_4826_, 0);
lean_dec(v_unused_4880_);
v___x_4848_ = v_r_4826_;
v_isShared_4849_ = v_isSharedCheck_4875_;
goto v_resetjp_4847_;
}
else
{
lean_dec(v_r_4826_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4875_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___y_4853_; lean_object* v___y_4854_; lean_object* v___y_4855_; lean_object* v___x_4863_; lean_object* v___y_4865_; 
v___x_4850_ = lean_nat_add(v___x_4820_, v_size_4822_);
lean_dec(v_size_4822_);
v___x_4851_ = lean_nat_add(v___x_4850_, v_size_4821_);
lean_dec(v___x_4850_);
v___x_4863_ = lean_nat_add(v___x_4820_, v_size_4838_);
if (lean_obj_tag(v_l_4842_) == 0)
{
lean_object* v_size_4873_; 
v_size_4873_ = lean_ctor_get(v_l_4842_, 0);
lean_inc(v_size_4873_);
v___y_4865_ = v_size_4873_;
goto v___jp_4864_;
}
else
{
lean_object* v___x_4874_; 
v___x_4874_ = lean_unsigned_to_nat(0u);
v___y_4865_ = v___x_4874_;
goto v___jp_4864_;
}
v___jp_4852_:
{
lean_object* v___x_4856_; lean_object* v___x_4858_; 
v___x_4856_ = lean_nat_add(v___y_4853_, v___y_4855_);
lean_dec(v___y_4855_);
lean_dec(v___y_4853_);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 4, v_r_4675_);
lean_ctor_set(v___x_4848_, 3, v_r_4843_);
lean_ctor_set(v___x_4848_, 2, v_v_4673_);
lean_ctor_set(v___x_4848_, 1, v_k_4672_);
lean_ctor_set(v___x_4848_, 0, v___x_4856_);
v___x_4858_ = v___x_4848_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4856_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4862_, 3, v_r_4843_);
lean_ctor_set(v_reuseFailAlloc_4862_, 4, v_r_4675_);
v___x_4858_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4860_; 
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 4, v___x_4858_);
lean_ctor_set(v___x_4836_, 3, v___y_4854_);
lean_ctor_set(v___x_4836_, 2, v_v_4841_);
lean_ctor_set(v___x_4836_, 1, v_k_4840_);
lean_ctor_set(v___x_4836_, 0, v___x_4851_);
v___x_4860_ = v___x_4836_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_k_4840_);
lean_ctor_set(v_reuseFailAlloc_4861_, 2, v_v_4841_);
lean_ctor_set(v_reuseFailAlloc_4861_, 3, v___y_4854_);
lean_ctor_set(v_reuseFailAlloc_4861_, 4, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
v___jp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4866_ = lean_nat_add(v___x_4863_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec(v___x_4863_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_l_4842_);
lean_ctor_set(v___x_4677_, 3, v_l_4825_);
lean_ctor_set(v___x_4677_, 2, v_v_4824_);
lean_ctor_set(v___x_4677_, 1, v_k_4823_);
lean_ctor_set(v___x_4677_, 0, v___x_4866_);
v___x_4868_ = v___x_4677_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4872_, 1, v_k_4823_);
lean_ctor_set(v_reuseFailAlloc_4872_, 2, v_v_4824_);
lean_ctor_set(v_reuseFailAlloc_4872_, 3, v_l_4825_);
lean_ctor_set(v_reuseFailAlloc_4872_, 4, v_l_4842_);
v___x_4868_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_nat_add(v___x_4820_, v_size_4821_);
if (lean_obj_tag(v_r_4843_) == 0)
{
lean_object* v_size_4870_; 
v_size_4870_ = lean_ctor_get(v_r_4843_, 0);
lean_inc(v_size_4870_);
v___y_4853_ = v___x_4869_;
v___y_4854_ = v___x_4868_;
v___y_4855_ = v_size_4870_;
goto v___jp_4852_;
}
else
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_unsigned_to_nat(0u);
v___y_4853_ = v___x_4869_;
v___y_4854_ = v___x_4868_;
v___y_4855_ = v___x_4871_;
goto v___jp_4852_;
}
}
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
lean_del_object(v___x_4677_);
v___x_4881_ = lean_nat_add(v___x_4820_, v_size_4822_);
lean_dec(v_size_4822_);
v___x_4882_ = lean_nat_add(v___x_4881_, v_size_4821_);
lean_dec(v___x_4881_);
v___x_4883_ = lean_nat_add(v___x_4820_, v_size_4821_);
v___x_4884_ = lean_nat_add(v___x_4883_, v_size_4839_);
lean_dec(v___x_4883_);
lean_inc_ref(v_r_4675_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 4, v_r_4675_);
lean_ctor_set(v___x_4836_, 3, v_r_4826_);
lean_ctor_set(v___x_4836_, 2, v_v_4673_);
lean_ctor_set(v___x_4836_, 1, v_k_4672_);
lean_ctor_set(v___x_4836_, 0, v___x_4884_);
v___x_4886_ = v___x_4836_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4899_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4899_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4899_, 3, v_r_4826_);
lean_ctor_set(v_reuseFailAlloc_4899_, 4, v_r_4675_);
v___x_4886_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_isSharedCheck_4893_ = !lean_is_exclusive(v_r_4675_);
if (v_isSharedCheck_4893_ == 0)
{
lean_object* v_unused_4894_; lean_object* v_unused_4895_; lean_object* v_unused_4896_; lean_object* v_unused_4897_; lean_object* v_unused_4898_; 
v_unused_4894_ = lean_ctor_get(v_r_4675_, 4);
lean_dec(v_unused_4894_);
v_unused_4895_ = lean_ctor_get(v_r_4675_, 3);
lean_dec(v_unused_4895_);
v_unused_4896_ = lean_ctor_get(v_r_4675_, 2);
lean_dec(v_unused_4896_);
v_unused_4897_ = lean_ctor_get(v_r_4675_, 1);
lean_dec(v_unused_4897_);
v_unused_4898_ = lean_ctor_get(v_r_4675_, 0);
lean_dec(v_unused_4898_);
v___x_4888_ = v_r_4675_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_dec(v_r_4675_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 4, v___x_4886_);
lean_ctor_set(v___x_4888_, 3, v_l_4825_);
lean_ctor_set(v___x_4888_, 2, v_v_4824_);
lean_ctor_set(v___x_4888_, 1, v_k_4823_);
lean_ctor_set(v___x_4888_, 0, v___x_4882_);
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_k_4823_);
lean_ctor_set(v_reuseFailAlloc_4892_, 2, v_v_4824_);
lean_ctor_set(v_reuseFailAlloc_4892_, 3, v_l_4825_);
lean_ctor_set(v_reuseFailAlloc_4892_, 4, v___x_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4906_; 
v_l_4906_ = lean_ctor_get(v_impl_4819_, 3);
lean_inc(v_l_4906_);
if (lean_obj_tag(v_l_4906_) == 0)
{
lean_object* v_r_4907_; lean_object* v_k_4908_; lean_object* v_v_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4920_; 
v_r_4907_ = lean_ctor_get(v_impl_4819_, 4);
v_k_4908_ = lean_ctor_get(v_impl_4819_, 1);
v_v_4909_ = lean_ctor_get(v_impl_4819_, 2);
v_isSharedCheck_4920_ = !lean_is_exclusive(v_impl_4819_);
if (v_isSharedCheck_4920_ == 0)
{
lean_object* v_unused_4921_; lean_object* v_unused_4922_; 
v_unused_4921_ = lean_ctor_get(v_impl_4819_, 3);
lean_dec(v_unused_4921_);
v_unused_4922_ = lean_ctor_get(v_impl_4819_, 0);
lean_dec(v_unused_4922_);
v___x_4911_ = v_impl_4819_;
v_isShared_4912_ = v_isSharedCheck_4920_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_r_4907_);
lean_inc(v_v_4909_);
lean_inc(v_k_4908_);
lean_dec(v_impl_4819_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4920_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4913_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4907_);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 3, v_r_4907_);
lean_ctor_set(v___x_4911_, 2, v_v_4673_);
lean_ctor_set(v___x_4911_, 1, v_k_4672_);
lean_ctor_set(v___x_4911_, 0, v___x_4820_);
v___x_4915_ = v___x_4911_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4919_, 3, v_r_4907_);
lean_ctor_set(v_reuseFailAlloc_4919_, 4, v_r_4907_);
v___x_4915_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4917_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v___x_4915_);
lean_ctor_set(v___x_4677_, 3, v_l_4906_);
lean_ctor_set(v___x_4677_, 2, v_v_4909_);
lean_ctor_set(v___x_4677_, 1, v_k_4908_);
lean_ctor_set(v___x_4677_, 0, v___x_4913_);
v___x_4917_ = v___x_4677_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_k_4908_);
lean_ctor_set(v_reuseFailAlloc_4918_, 2, v_v_4909_);
lean_ctor_set(v_reuseFailAlloc_4918_, 3, v_l_4906_);
lean_ctor_set(v_reuseFailAlloc_4918_, 4, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
else
{
lean_object* v_r_4923_; 
v_r_4923_ = lean_ctor_get(v_impl_4819_, 4);
lean_inc(v_r_4923_);
if (lean_obj_tag(v_r_4923_) == 0)
{
lean_object* v_k_4924_; lean_object* v_v_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4948_; 
v_k_4924_ = lean_ctor_get(v_impl_4819_, 1);
v_v_4925_ = lean_ctor_get(v_impl_4819_, 2);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_impl_4819_);
if (v_isSharedCheck_4948_ == 0)
{
lean_object* v_unused_4949_; lean_object* v_unused_4950_; lean_object* v_unused_4951_; 
v_unused_4949_ = lean_ctor_get(v_impl_4819_, 4);
lean_dec(v_unused_4949_);
v_unused_4950_ = lean_ctor_get(v_impl_4819_, 3);
lean_dec(v_unused_4950_);
v_unused_4951_ = lean_ctor_get(v_impl_4819_, 0);
lean_dec(v_unused_4951_);
v___x_4927_ = v_impl_4819_;
v_isShared_4928_ = v_isSharedCheck_4948_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_v_4925_);
lean_inc(v_k_4924_);
lean_dec(v_impl_4819_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4948_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v_k_4929_; lean_object* v_v_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4944_; 
v_k_4929_ = lean_ctor_get(v_r_4923_, 1);
v_v_4930_ = lean_ctor_get(v_r_4923_, 2);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_r_4923_);
if (v_isSharedCheck_4944_ == 0)
{
lean_object* v_unused_4945_; lean_object* v_unused_4946_; lean_object* v_unused_4947_; 
v_unused_4945_ = lean_ctor_get(v_r_4923_, 4);
lean_dec(v_unused_4945_);
v_unused_4946_ = lean_ctor_get(v_r_4923_, 3);
lean_dec(v_unused_4946_);
v_unused_4947_ = lean_ctor_get(v_r_4923_, 0);
lean_dec(v_unused_4947_);
v___x_4932_ = v_r_4923_;
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_v_4930_);
lean_inc(v_k_4929_);
lean_dec(v_r_4923_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4934_ = lean_unsigned_to_nat(3u);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 4, v_l_4906_);
lean_ctor_set(v___x_4932_, 3, v_l_4906_);
lean_ctor_set(v___x_4932_, 2, v_v_4925_);
lean_ctor_set(v___x_4932_, 1, v_k_4924_);
lean_ctor_set(v___x_4932_, 0, v___x_4820_);
v___x_4936_ = v___x_4932_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_k_4924_);
lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_v_4925_);
lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_l_4906_);
lean_ctor_set(v_reuseFailAlloc_4943_, 4, v_l_4906_);
v___x_4936_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4938_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 4, v_l_4906_);
lean_ctor_set(v___x_4927_, 2, v_v_4673_);
lean_ctor_set(v___x_4927_, 1, v_k_4672_);
lean_ctor_set(v___x_4927_, 0, v___x_4820_);
v___x_4938_ = v___x_4927_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4942_, 3, v_l_4906_);
lean_ctor_set(v_reuseFailAlloc_4942_, 4, v_l_4906_);
v___x_4938_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4940_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v___x_4938_);
lean_ctor_set(v___x_4677_, 3, v___x_4936_);
lean_ctor_set(v___x_4677_, 2, v_v_4930_);
lean_ctor_set(v___x_4677_, 1, v_k_4929_);
lean_ctor_set(v___x_4677_, 0, v___x_4934_);
v___x_4940_ = v___x_4677_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4934_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v_k_4929_);
lean_ctor_set(v_reuseFailAlloc_4941_, 2, v_v_4930_);
lean_ctor_set(v_reuseFailAlloc_4941_, 3, v___x_4936_);
lean_ctor_set(v_reuseFailAlloc_4941_, 4, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4954_; 
v___x_4952_ = lean_unsigned_to_nat(2u);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 4, v_r_4923_);
lean_ctor_set(v___x_4677_, 3, v_impl_4819_);
lean_ctor_set(v___x_4677_, 0, v___x_4952_);
v___x_4954_ = v___x_4677_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4952_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4955_, 3, v_impl_4819_);
lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_r_4923_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = lean_unsigned_to_nat(1u);
v___x_4958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
lean_ctor_set(v___x_4958_, 1, v_k_4668_);
lean_ctor_set(v___x_4958_, 2, v_v_4669_);
lean_ctor_set(v___x_4958_, 3, v_t_4670_);
lean_ctor_set(v___x_4958_, 4, v_t_4670_);
return v___x_4958_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_4959_, lean_object* v_t_4960_){
_start:
{
if (lean_obj_tag(v_t_4960_) == 0)
{
lean_object* v_k_4961_; lean_object* v_l_4962_; lean_object* v_r_4963_; uint8_t v___x_4964_; 
v_k_4961_ = lean_ctor_get(v_t_4960_, 1);
v_l_4962_ = lean_ctor_get(v_t_4960_, 3);
v_r_4963_ = lean_ctor_get(v_t_4960_, 4);
v___x_4964_ = lean_nat_dec_lt(v_k_4961_, v_k_4959_);
if (v___x_4964_ == 0)
{
uint8_t v___x_4965_; 
v___x_4965_ = lean_nat_dec_eq(v_k_4961_, v_k_4959_);
if (v___x_4965_ == 0)
{
v_t_4960_ = v_r_4963_;
goto _start;
}
else
{
return v___x_4965_;
}
}
else
{
v_t_4960_ = v_l_4962_;
goto _start;
}
}
else
{
uint8_t v___x_4968_; 
v___x_4968_ = 0;
return v___x_4968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_4969_, lean_object* v_t_4970_){
_start:
{
uint8_t v_res_4971_; lean_object* v_r_4972_; 
v_res_4971_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4969_, v_t_4970_);
lean_dec(v_t_4970_);
lean_dec(v_k_4969_);
v_r_4972_ = lean_box(v_res_4971_);
return v_r_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_4973_, lean_object* v_e_4974_){
_start:
{
lean_object* v_defaultInstances_4975_; lean_object* v_priorities_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_5003_; 
v_defaultInstances_4975_ = lean_ctor_get(v_d_4973_, 0);
v_priorities_4976_ = lean_ctor_get(v_d_4973_, 1);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_d_4973_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4978_ = v_d_4973_;
v_isShared_4979_ = v_isSharedCheck_5003_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_priorities_4976_);
lean_inc(v_defaultInstances_4975_);
lean_dec(v_d_4973_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_5003_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v_className_4980_; lean_object* v_instanceName_4981_; lean_object* v_priority_4982_; lean_object* v___y_4984_; uint8_t v___x_5000_; 
v_className_4980_ = lean_ctor_get(v_e_4974_, 0);
lean_inc(v_className_4980_);
v_instanceName_4981_ = lean_ctor_get(v_e_4974_, 1);
lean_inc(v_instanceName_4981_);
v_priority_4982_ = lean_ctor_get(v_e_4974_, 2);
lean_inc(v_priority_4982_);
lean_dec_ref(v_e_4974_);
v___x_5000_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_4982_, v_priorities_4976_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = lean_box(0);
lean_inc(v_priority_4982_);
v___x_5002_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_4982_, v___x_5001_, v_priorities_4976_);
v___y_4984_ = v___x_5002_;
goto v___jp_4983_;
}
else
{
v___y_4984_ = v_priorities_4976_;
goto v___jp_4983_;
}
v___jp_4983_:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_4975_, v_className_4980_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4991_; 
v___x_4986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4986_, 0, v_instanceName_4981_);
lean_ctor_set(v___x_4986_, 1, v_priority_4982_);
v___x_4987_ = lean_box(0);
v___x_4988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4980_, v___x_4988_, v_defaultInstances_4975_);
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 1, v___y_4984_);
lean_ctor_set(v___x_4978_, 0, v___x_4989_);
v___x_4991_ = v___x_4978_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___y_4984_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
else
{
lean_object* v_val_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4998_; 
v_val_4993_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_val_4993_);
lean_dec_ref(v___x_4985_);
v___x_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4994_, 0, v_instanceName_4981_);
lean_ctor_set(v___x_4994_, 1, v_priority_4982_);
v___x_4995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
lean_ctor_set(v___x_4995_, 1, v_val_4993_);
v___x_4996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4980_, v___x_4995_, v_defaultInstances_4975_);
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 1, v___y_4984_);
lean_ctor_set(v___x_4978_, 0, v___x_4996_);
v___x_4998_ = v___x_4978_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___y_4984_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5004_, lean_object* v_k_5005_, lean_object* v_t_5006_){
_start:
{
uint8_t v___x_5007_; 
v___x_5007_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5005_, v_t_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5008_, lean_object* v_k_5009_, lean_object* v_t_5010_){
_start:
{
uint8_t v_res_5011_; lean_object* v_r_5012_; 
v_res_5011_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5008_, v_k_5009_, v_t_5010_);
lean_dec(v_t_5010_);
lean_dec(v_k_5009_);
v_r_5012_ = lean_box(v_res_5011_);
return v_r_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5013_, lean_object* v_k_5014_, lean_object* v_v_5015_, lean_object* v_t_5016_, lean_object* v_hl_5017_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5014_, v_v_5015_, v_t_5016_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5019_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = lean_array_mk(v_es_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5021_, size_t v_i_5022_, size_t v_stop_5023_, lean_object* v_b_5024_){
_start:
{
uint8_t v___x_5025_; 
v___x_5025_ = lean_usize_dec_eq(v_i_5022_, v_stop_5023_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5027_; size_t v___x_5028_; size_t v___x_5029_; 
v___x_5026_ = lean_array_uget_borrowed(v_as_5021_, v_i_5022_);
lean_inc(v___x_5026_);
v___x_5027_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5024_, v___x_5026_);
v___x_5028_ = ((size_t)1ULL);
v___x_5029_ = lean_usize_add(v_i_5022_, v___x_5028_);
v_i_5022_ = v___x_5029_;
v_b_5024_ = v___x_5027_;
goto _start;
}
else
{
return v_b_5024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5031_, lean_object* v_i_5032_, lean_object* v_stop_5033_, lean_object* v_b_5034_){
_start:
{
size_t v_i_boxed_5035_; size_t v_stop_boxed_5036_; lean_object* v_res_5037_; 
v_i_boxed_5035_ = lean_unbox_usize(v_i_5032_);
lean_dec(v_i_5032_);
v_stop_boxed_5036_ = lean_unbox_usize(v_stop_5033_);
lean_dec(v_stop_5033_);
v_res_5037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_5031_, v_i_boxed_5035_, v_stop_boxed_5036_, v_b_5034_);
lean_dec_ref(v_as_5031_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_5038_, size_t v_i_5039_, size_t v_stop_5040_, lean_object* v_b_5041_){
_start:
{
lean_object* v___y_5043_; uint8_t v___x_5047_; 
v___x_5047_ = lean_usize_dec_eq(v_i_5039_, v_stop_5040_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; uint8_t v___x_5051_; 
v___x_5048_ = lean_array_uget_borrowed(v_as_5038_, v_i_5039_);
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = lean_array_get_size(v___x_5048_);
v___x_5051_ = lean_nat_dec_lt(v___x_5049_, v___x_5050_);
if (v___x_5051_ == 0)
{
v___y_5043_ = v_b_5041_;
goto v___jp_5042_;
}
else
{
uint8_t v___x_5052_; 
v___x_5052_ = lean_nat_dec_le(v___x_5050_, v___x_5050_);
if (v___x_5052_ == 0)
{
if (v___x_5051_ == 0)
{
v___y_5043_ = v_b_5041_;
goto v___jp_5042_;
}
else
{
size_t v___x_5053_; size_t v___x_5054_; lean_object* v___x_5055_; 
v___x_5053_ = ((size_t)0ULL);
v___x_5054_ = lean_usize_of_nat(v___x_5050_);
v___x_5055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5048_, v___x_5053_, v___x_5054_, v_b_5041_);
v___y_5043_ = v___x_5055_;
goto v___jp_5042_;
}
}
else
{
size_t v___x_5056_; size_t v___x_5057_; lean_object* v___x_5058_; 
v___x_5056_ = ((size_t)0ULL);
v___x_5057_ = lean_usize_of_nat(v___x_5050_);
v___x_5058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5048_, v___x_5056_, v___x_5057_, v_b_5041_);
v___y_5043_ = v___x_5058_;
goto v___jp_5042_;
}
}
}
else
{
return v_b_5041_;
}
v___jp_5042_:
{
size_t v___x_5044_; size_t v___x_5045_; 
v___x_5044_ = ((size_t)1ULL);
v___x_5045_ = lean_usize_add(v_i_5039_, v___x_5044_);
v_i_5039_ = v___x_5045_;
v_b_5041_ = v___y_5043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5059_, lean_object* v_i_5060_, lean_object* v_stop_5061_, lean_object* v_b_5062_){
_start:
{
size_t v_i_boxed_5063_; size_t v_stop_boxed_5064_; lean_object* v_res_5065_; 
v_i_boxed_5063_ = lean_unbox_usize(v_i_5060_);
lean_dec(v_i_5060_);
v_stop_boxed_5064_ = lean_unbox_usize(v_stop_5061_);
lean_dec(v_stop_5061_);
v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5059_, v_i_boxed_5063_, v_stop_boxed_5064_, v_b_5062_);
lean_dec_ref(v_as_5059_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5066_, lean_object* v_as_5067_){
_start:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v___x_5068_ = lean_unsigned_to_nat(0u);
v___x_5069_ = lean_array_get_size(v_as_5067_);
v___x_5070_ = lean_nat_dec_lt(v___x_5068_, v___x_5069_);
if (v___x_5070_ == 0)
{
return v_initState_5066_;
}
else
{
uint8_t v___x_5071_; 
v___x_5071_ = lean_nat_dec_le(v___x_5069_, v___x_5069_);
if (v___x_5071_ == 0)
{
if (v___x_5070_ == 0)
{
return v_initState_5066_;
}
else
{
size_t v___x_5072_; size_t v___x_5073_; lean_object* v___x_5074_; 
v___x_5072_ = ((size_t)0ULL);
v___x_5073_ = lean_usize_of_nat(v___x_5069_);
v___x_5074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5067_, v___x_5072_, v___x_5073_, v_initState_5066_);
return v___x_5074_;
}
}
else
{
size_t v___x_5075_; size_t v___x_5076_; lean_object* v___x_5077_; 
v___x_5075_ = ((size_t)0ULL);
v___x_5076_ = lean_usize_of_nat(v___x_5069_);
v___x_5077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5067_, v___x_5075_, v___x_5076_, v_initState_5066_);
return v___x_5077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5078_, lean_object* v_as_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5078_, v_as_5079_);
lean_dec_ref(v_as_5079_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5083_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5082_, v_es_5081_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5084_);
lean_dec_ref(v_es_5084_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5103_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v___x_5110_; lean_object* v_nextMacroScope_5111_; lean_object* v_ngen_5112_; lean_object* v_auxDeclNGen_5113_; lean_object* v_traceState_5114_; lean_object* v_messages_5115_; lean_object* v_infoState_5116_; lean_object* v_snapshotTasks_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5143_; 
v___x_5110_ = lean_st_ref_take(v___y_5108_);
v_nextMacroScope_5111_ = lean_ctor_get(v___x_5110_, 1);
v_ngen_5112_ = lean_ctor_get(v___x_5110_, 2);
v_auxDeclNGen_5113_ = lean_ctor_get(v___x_5110_, 3);
v_traceState_5114_ = lean_ctor_get(v___x_5110_, 4);
v_messages_5115_ = lean_ctor_get(v___x_5110_, 6);
v_infoState_5116_ = lean_ctor_get(v___x_5110_, 7);
v_snapshotTasks_5117_ = lean_ctor_get(v___x_5110_, 8);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5143_ == 0)
{
lean_object* v_unused_5144_; lean_object* v_unused_5145_; 
v_unused_5144_ = lean_ctor_get(v___x_5110_, 5);
lean_dec(v_unused_5144_);
v_unused_5145_ = lean_ctor_get(v___x_5110_, 0);
lean_dec(v_unused_5145_);
v___x_5119_ = v___x_5110_;
v_isShared_5120_ = v_isSharedCheck_5143_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_snapshotTasks_5117_);
lean_inc(v_infoState_5116_);
lean_inc(v_messages_5115_);
lean_inc(v_traceState_5114_);
lean_inc(v_auxDeclNGen_5113_);
lean_inc(v_ngen_5112_);
lean_inc(v_nextMacroScope_5111_);
lean_dec(v___x_5110_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5143_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5121_; lean_object* v___x_5123_; 
v___x_5121_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 5, v___x_5121_);
lean_ctor_set(v___x_5119_, 0, v_env_5106_);
v___x_5123_ = v___x_5119_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_env_5106_);
lean_ctor_set(v_reuseFailAlloc_5142_, 1, v_nextMacroScope_5111_);
lean_ctor_set(v_reuseFailAlloc_5142_, 2, v_ngen_5112_);
lean_ctor_set(v_reuseFailAlloc_5142_, 3, v_auxDeclNGen_5113_);
lean_ctor_set(v_reuseFailAlloc_5142_, 4, v_traceState_5114_);
lean_ctor_set(v_reuseFailAlloc_5142_, 5, v___x_5121_);
lean_ctor_set(v_reuseFailAlloc_5142_, 6, v_messages_5115_);
lean_ctor_set(v_reuseFailAlloc_5142_, 7, v_infoState_5116_);
lean_ctor_set(v_reuseFailAlloc_5142_, 8, v_snapshotTasks_5117_);
v___x_5123_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v_mctx_5126_; lean_object* v_zetaDeltaFVarIds_5127_; lean_object* v_postponed_5128_; lean_object* v_diag_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5140_; 
v___x_5124_ = lean_st_ref_set(v___y_5108_, v___x_5123_);
v___x_5125_ = lean_st_ref_take(v___y_5107_);
v_mctx_5126_ = lean_ctor_get(v___x_5125_, 0);
v_zetaDeltaFVarIds_5127_ = lean_ctor_get(v___x_5125_, 2);
v_postponed_5128_ = lean_ctor_get(v___x_5125_, 3);
v_diag_5129_ = lean_ctor_get(v___x_5125_, 4);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; 
v_unused_5141_ = lean_ctor_get(v___x_5125_, 1);
lean_dec(v_unused_5141_);
v___x_5131_ = v___x_5125_;
v_isShared_5132_ = v_isSharedCheck_5140_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_diag_5129_);
lean_inc(v_postponed_5128_);
lean_inc(v_zetaDeltaFVarIds_5127_);
lean_inc(v_mctx_5126_);
lean_dec(v___x_5125_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5140_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5133_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v___x_5133_);
v___x_5135_ = v___x_5131_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_mctx_5126_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v___x_5133_);
lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_zetaDeltaFVarIds_5127_);
lean_ctor_set(v_reuseFailAlloc_5139_, 3, v_postponed_5128_);
lean_ctor_set(v_reuseFailAlloc_5139_, 4, v_diag_5129_);
v___x_5135_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_st_ref_set(v___y_5107_, v___x_5135_);
v___x_5137_ = lean_box(0);
v___x_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
return v___x_5138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec(v___y_5147_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_){
_start:
{
lean_object* v___x_5157_; 
v___x_5157_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5151_, v___y_5153_, v___y_5155_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
return v_res_5164_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5166_; lean_object* v___x_5167_; 
v___x_5166_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5167_ = l_Lean_stringToMessageData(v___x_5166_);
return v___x_5167_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5169_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5170_ = l_Lean_stringToMessageData(v___x_5169_);
return v___x_5170_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5172_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5173_ = l_Lean_stringToMessageData(v___x_5172_);
return v___x_5173_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5175_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5176_ = l_Lean_stringToMessageData(v___x_5175_);
return v___x_5176_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5179_ = l_Lean_stringToMessageData(v___x_5178_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5180_, lean_object* v_prio_5181_, lean_object* v_x_5182_, lean_object* v_type_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l_Lean_Expr_getAppFn(v_type_5183_);
if (lean_obj_tag(v___x_5189_) == 4)
{
lean_object* v_declName_5190_; lean_object* v___y_5192_; lean_object* v___y_5193_; lean_object* v___y_5194_; lean_object* v___y_5195_; lean_object* v___x_5205_; lean_object* v_env_5206_; uint8_t v___x_5207_; 
v_declName_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_declName_5190_);
lean_dec_ref(v___x_5189_);
v___x_5205_ = lean_st_ref_get(v___y_5187_);
v_env_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc_ref(v_env_5206_);
lean_dec(v___x_5205_);
lean_inc(v_declName_5190_);
v___x_5207_ = lean_is_class(v_env_5206_, v_declName_5190_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_dec(v_prio_5181_);
v___x_5208_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5209_ = l_Lean_MessageData_ofConstName(v_declName_5180_, v___x_5207_);
v___x_5210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5208_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
v___x_5211_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5210_);
lean_ctor_set(v___x_5212_, 1, v___x_5211_);
lean_inc(v_declName_5190_);
v___x_5213_ = l_Lean_MessageData_ofName(v_declName_5190_);
v___x_5214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5212_);
lean_ctor_set(v___x_5214_, 1, v___x_5213_);
v___x_5215_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5214_);
lean_ctor_set(v___x_5216_, 1, v___x_5215_);
v___x_5217_ = l_Lean_MessageData_ofConstName(v_declName_5190_, v___x_5207_);
v___x_5218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5216_);
lean_ctor_set(v___x_5218_, 1, v___x_5217_);
v___x_5219_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5218_);
lean_ctor_set(v___x_5220_, 1, v___x_5219_);
v___x_5221_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5220_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
return v___x_5221_;
}
else
{
v___y_5192_ = v___y_5184_;
v___y_5193_ = v___y_5185_;
v___y_5194_ = v___y_5186_;
v___y_5195_ = v___y_5187_;
goto v___jp_5191_;
}
v___jp_5191_:
{
lean_object* v___x_5196_; lean_object* v_env_5197_; lean_object* v___x_5198_; lean_object* v_toEnvExtension_5199_; lean_object* v_asyncMode_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5196_ = lean_st_ref_get(v___y_5195_);
v_env_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc_ref(v_env_5197_);
lean_dec(v___x_5196_);
v___x_5198_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc_ref(v_toEnvExtension_5199_);
v_asyncMode_5200_ = lean_ctor_get(v_toEnvExtension_5199_, 2);
lean_inc(v_asyncMode_5200_);
lean_dec_ref(v_toEnvExtension_5199_);
v___x_5201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5201_, 0, v_declName_5190_);
lean_ctor_set(v___x_5201_, 1, v_declName_5180_);
lean_ctor_set(v___x_5201_, 2, v_prio_5181_);
v___x_5202_ = lean_box(0);
v___x_5203_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5198_, v_env_5197_, v___x_5201_, v_asyncMode_5200_, v___x_5202_);
lean_dec(v_asyncMode_5200_);
v___x_5204_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5203_, v___y_5193_, v___y_5195_);
return v___x_5204_;
}
}
else
{
lean_object* v___x_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
lean_dec_ref(v___x_5189_);
lean_dec(v_prio_5181_);
v___x_5222_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5223_ = 0;
v___x_5224_ = l_Lean_MessageData_ofConstName(v_declName_5180_, v___x_5223_);
v___x_5225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5222_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
v___x_5226_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5225_);
lean_ctor_set(v___x_5227_, 1, v___x_5226_);
v___x_5228_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5227_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
return v___x_5228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5229_, lean_object* v_prio_5230_, lean_object* v_x_5231_, lean_object* v_type_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5229_, v_prio_5230_, v_x_5231_, v_type_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec_ref(v_type_5232_);
lean_dec_ref(v_x_5231_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5239_, lean_object* v_prio_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_){
_start:
{
lean_object* v___x_5246_; lean_object* v_env_5247_; uint8_t v___x_5248_; lean_object* v___x_5249_; 
v___x_5246_ = lean_st_ref_get(v_a_5244_);
v_env_5247_ = lean_ctor_get(v___x_5246_, 0);
lean_inc_ref(v_env_5247_);
lean_dec(v___x_5246_);
v___x_5248_ = 0;
lean_inc(v_declName_5239_);
v___x_5249_ = l_Lean_Environment_find_x3f(v_env_5247_, v_declName_5239_, v___x_5248_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
lean_dec(v_prio_5240_);
v___x_5250_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5251_ = l_Lean_MessageData_ofConstName(v_declName_5239_, v___x_5248_);
v___x_5252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5250_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5252_);
lean_ctor_set(v___x_5254_, 1, v___x_5253_);
v___x_5255_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5254_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
lean_dec(v_a_5244_);
lean_dec_ref(v_a_5243_);
lean_dec(v_a_5242_);
lean_dec_ref(v_a_5241_);
return v___x_5255_;
}
else
{
lean_object* v_val_5256_; lean_object* v___f_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; 
v_val_5256_ = lean_ctor_get(v___x_5249_, 0);
lean_inc(v_val_5256_);
lean_dec_ref(v___x_5249_);
v___f_5257_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5257_, 0, v_declName_5239_);
lean_closure_set(v___f_5257_, 1, v_prio_5240_);
v___x_5258_ = l_Lean_ConstantInfo_type(v_val_5256_);
lean_dec(v_val_5256_);
v___x_5259_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5258_, v___f_5257_, v___x_5248_, v___x_5248_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
return v___x_5259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5260_, lean_object* v_prio_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Lean_Meta_addDefaultInstance(v_declName_5260_, v_prio_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
return v_res_5267_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5269_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5270_ = l_Lean_stringToMessageData(v___x_5269_);
return v___x_5270_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5273_ = l_Lean_stringToMessageData(v___x_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5277_, uint8_t v_kind_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___y_5288_; 
v___x_5282_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5283_ = l_Lean_MessageData_ofName(v_name_5277_);
v___x_5284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5282_);
lean_ctor_set(v___x_5284_, 1, v___x_5283_);
v___x_5285_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5284_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
switch(v_kind_5278_)
{
case 0:
{
lean_object* v___x_5295_; 
v___x_5295_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5288_ = v___x_5295_;
goto v___jp_5287_;
}
case 1:
{
lean_object* v___x_5296_; 
v___x_5296_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5288_ = v___x_5296_;
goto v___jp_5287_;
}
default: 
{
lean_object* v___x_5297_; 
v___x_5297_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5288_ = v___x_5297_;
goto v___jp_5287_;
}
}
v___jp_5287_:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___y_5288_);
v___x_5290_ = l_Lean_MessageData_ofFormat(v___x_5289_);
v___x_5291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5286_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
v___x_5292_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5291_);
lean_ctor_set(v___x_5293_, 1, v___x_5292_);
v___x_5294_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5293_, v___y_5279_, v___y_5280_);
return v___x_5294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5298_, lean_object* v_kind_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
uint8_t v_kind_boxed_5303_; lean_object* v_res_5304_; 
v_kind_boxed_5303_ = lean_unbox(v_kind_5299_);
v_res_5304_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5298_, v_kind_boxed_5303_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5305_, lean_object* v___x_5306_, lean_object* v___x_5307_, lean_object* v_declName_5308_, lean_object* v_stx_5309_, uint8_t v_kind_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5314_ = lean_unsigned_to_nat(1u);
v___x_5315_ = l_Lean_Syntax_getArg(v_stx_5309_, v___x_5314_);
lean_inc_ref(v___y_5311_);
v___x_5316_ = l_Lean_getAttrParamOptPrio(v___x_5315_, v___y_5311_, v___y_5312_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___y_5319_; lean_object* v___y_5320_; uint8_t v___x_5351_; uint8_t v___x_5352_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_a_5317_);
lean_dec_ref(v___x_5316_);
v___x_5351_ = 0;
v___x_5352_ = l_Lean_instBEqAttributeKind_beq(v_kind_5310_, v___x_5351_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; 
lean_dec(v_a_5317_);
lean_dec(v_declName_5308_);
lean_dec(v___x_5306_);
lean_dec(v___x_5305_);
v___x_5353_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5307_, v_kind_5310_, v___y_5311_, v___y_5312_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
return v___x_5353_;
}
else
{
lean_dec(v___x_5307_);
v___y_5319_ = v___y_5311_;
v___y_5320_ = v___y_5312_;
goto v___jp_5318_;
}
v___jp_5318_:
{
lean_object* v___x_5321_; uint8_t v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; size_t v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; uint8_t v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5321_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_5322_ = 0;
v___x_5323_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5324_ = lean_unsigned_to_nat(32u);
v___x_5325_ = lean_mk_empty_array_with_capacity(v___x_5324_);
v___x_5326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5327_ = ((size_t)5ULL);
lean_inc_n(v___x_5305_, 2);
v___x_5328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
lean_ctor_set(v___x_5328_, 1, v___x_5325_);
lean_ctor_set(v___x_5328_, 2, v___x_5305_);
lean_ctor_set(v___x_5328_, 3, v___x_5305_);
lean_ctor_set_usize(v___x_5328_, 4, v___x_5327_);
v___x_5329_ = lean_box(1);
lean_inc_ref(v___x_5328_);
v___x_5330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5323_);
lean_ctor_set(v___x_5330_, 1, v___x_5328_);
lean_ctor_set(v___x_5330_, 2, v___x_5329_);
v___x_5331_ = lean_mk_empty_array_with_capacity(v___x_5305_);
v___x_5332_ = lean_box(0);
v___x_5333_ = 1;
lean_inc(v___x_5305_);
lean_inc(v___x_5306_);
v___x_5334_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5334_, 0, v___x_5321_);
lean_ctor_set(v___x_5334_, 1, v___x_5306_);
lean_ctor_set(v___x_5334_, 2, v___x_5330_);
lean_ctor_set(v___x_5334_, 3, v___x_5331_);
lean_ctor_set(v___x_5334_, 4, v___x_5332_);
lean_ctor_set(v___x_5334_, 5, v___x_5305_);
lean_ctor_set(v___x_5334_, 6, v___x_5332_);
lean_ctor_set_uint8(v___x_5334_, sizeof(void*)*7, v___x_5322_);
lean_ctor_set_uint8(v___x_5334_, sizeof(void*)*7 + 1, v___x_5322_);
lean_ctor_set_uint8(v___x_5334_, sizeof(void*)*7 + 2, v___x_5322_);
lean_ctor_set_uint8(v___x_5334_, sizeof(void*)*7 + 3, v___x_5333_);
lean_inc_n(v___x_5305_, 2);
v___x_5335_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_5335_, 0, v___x_5305_);
lean_ctor_set(v___x_5335_, 1, v___x_5305_);
lean_ctor_set(v___x_5335_, 2, v___x_5305_);
lean_ctor_set(v___x_5335_, 3, v___x_5323_);
lean_ctor_set(v___x_5335_, 4, v___x_5323_);
lean_ctor_set(v___x_5335_, 5, v___x_5323_);
lean_ctor_set(v___x_5335_, 6, v___x_5323_);
lean_ctor_set(v___x_5335_, 7, v___x_5323_);
lean_ctor_set(v___x_5335_, 8, v___x_5323_);
v___x_5336_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5337_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5335_);
lean_ctor_set(v___x_5338_, 1, v___x_5336_);
lean_ctor_set(v___x_5338_, 2, v___x_5306_);
lean_ctor_set(v___x_5338_, 3, v___x_5328_);
lean_ctor_set(v___x_5338_, 4, v___x_5337_);
v___x_5339_ = lean_st_mk_ref(v___x_5338_);
lean_inc(v___x_5339_);
v___x_5340_ = l_Lean_Meta_addDefaultInstance(v_declName_5308_, v_a_5317_, v___x_5334_, v___x_5339_, v___y_5319_, v___y_5320_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5349_; 
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5349_ == 0)
{
lean_object* v_unused_5350_; 
v_unused_5350_ = lean_ctor_get(v___x_5340_, 0);
lean_dec(v_unused_5350_);
v___x_5342_ = v___x_5340_;
v_isShared_5343_ = v_isSharedCheck_5349_;
goto v_resetjp_5341_;
}
else
{
lean_dec(v___x_5340_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5349_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5347_; 
v___x_5344_ = lean_st_ref_get(v___x_5339_);
lean_dec(v___x_5339_);
lean_dec(v___x_5344_);
v___x_5345_ = lean_box(0);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 0, v___x_5345_);
v___x_5347_ = v___x_5342_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
else
{
lean_dec(v___x_5339_);
return v___x_5340_;
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v_declName_5308_);
lean_dec(v___x_5307_);
lean_dec(v___x_5306_);
lean_dec(v___x_5305_);
v_a_5354_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5316_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5316_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5362_, lean_object* v___x_5363_, lean_object* v___x_5364_, lean_object* v_declName_5365_, lean_object* v_stx_5366_, lean_object* v_kind_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
uint8_t v_kind_boxed_5371_; lean_object* v_res_5372_; 
v_kind_boxed_5371_ = lean_unbox(v_kind_5367_);
v_res_5372_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5362_, v___x_5363_, v___x_5364_, v_declName_5365_, v_stx_5366_, v_kind_boxed_5371_, v___y_5368_, v___y_5369_);
lean_dec(v_stx_5366_);
return v_res_5372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5374_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5375_ = l_Lean_stringToMessageData(v___x_5374_);
return v___x_5375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5377_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5378_ = l_Lean_stringToMessageData(v___x_5377_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5379_, lean_object* v_decl_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5384_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5385_ = l_Lean_MessageData_ofName(v___x_5379_);
v___x_5386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5384_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5386_);
lean_ctor_set(v___x_5388_, 1, v___x_5387_);
v___x_5389_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5388_, v___y_5381_, v___y_5382_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5390_, lean_object* v_decl_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5390_, v_decl_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v_decl_5391_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5428_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5429_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5430_ = l_Lean_registerBuiltinAttribute(v___x_5429_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; 
lean_dec_ref(v___x_5430_);
v___x_5431_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5432_ = 0;
v___x_5433_ = l_Lean_registerTraceClass(v___x_5431_, v___x_5432_, v___x_5428_);
return v___x_5433_;
}
else
{
return v___x_5430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5436_, lean_object* v_name_5437_, uint8_t v_kind_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___x_5442_; 
v___x_5442_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5437_, v_kind_5438_, v___y_5439_, v___y_5440_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5443_, lean_object* v_name_5444_, lean_object* v_kind_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
uint8_t v_kind_boxed_5449_; lean_object* v_res_5450_; 
v_kind_boxed_5449_ = lean_unbox(v_kind_5445_);
v_res_5450_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5443_, v_name_5444_, v_kind_boxed_5449_, v___y_5446_, v___y_5447_);
lean_dec(v___y_5447_);
lean_dec_ref(v___y_5446_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5451_, lean_object* v_toPure_5452_, lean_object* v_____do__lift_5453_){
_start:
{
lean_object* v___x_5454_; lean_object* v_toEnvExtension_5455_; lean_object* v_asyncMode_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v_priorities_5459_; lean_object* v___x_5460_; 
v___x_5454_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc_ref(v_toEnvExtension_5455_);
v_asyncMode_5456_ = lean_ctor_get(v_toEnvExtension_5455_, 2);
lean_inc(v_asyncMode_5456_);
lean_dec_ref(v_toEnvExtension_5455_);
v___x_5457_ = lean_box(0);
v___x_5458_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5451_, v___x_5454_, v_____do__lift_5453_, v_asyncMode_5456_, v___x_5457_);
lean_dec(v_asyncMode_5456_);
v_priorities_5459_ = lean_ctor_get(v___x_5458_, 1);
lean_inc(v_priorities_5459_);
lean_dec(v___x_5458_);
v___x_5460_ = lean_apply_2(v_toPure_5452_, lean_box(0), v_priorities_5459_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5461_, lean_object* v_inst_5462_){
_start:
{
lean_object* v_toApplicative_5463_; lean_object* v_toBind_5464_; lean_object* v_getEnv_5465_; lean_object* v_toPure_5466_; lean_object* v___x_5467_; lean_object* v___f_5468_; lean_object* v___x_5469_; 
v_toApplicative_5463_ = lean_ctor_get(v_inst_5461_, 0);
lean_inc_ref(v_toApplicative_5463_);
v_toBind_5464_ = lean_ctor_get(v_inst_5461_, 1);
lean_inc(v_toBind_5464_);
lean_dec_ref(v_inst_5461_);
v_getEnv_5465_ = lean_ctor_get(v_inst_5462_, 0);
lean_inc(v_getEnv_5465_);
lean_dec_ref(v_inst_5462_);
v_toPure_5466_ = lean_ctor_get(v_toApplicative_5463_, 1);
lean_inc(v_toPure_5466_);
lean_dec_ref(v_toApplicative_5463_);
v___x_5467_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5468_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5468_, 0, v___x_5467_);
lean_closure_set(v___f_5468_, 1, v_toPure_5466_);
v___x_5469_ = lean_apply_4(v_toBind_5464_, lean_box(0), lean_box(0), v_getEnv_5465_, v___f_5468_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5470_, lean_object* v_inst_5471_, lean_object* v_inst_5472_){
_start:
{
lean_object* v___x_5473_; 
v___x_5473_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5471_, v_inst_5472_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5474_, lean_object* v_className_5475_, lean_object* v_toPure_5476_, lean_object* v_____do__lift_5477_){
_start:
{
lean_object* v___x_5478_; lean_object* v_toEnvExtension_5479_; lean_object* v_asyncMode_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v_defaultInstances_5483_; lean_object* v___x_5484_; 
v___x_5478_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc_ref(v_toEnvExtension_5479_);
v_asyncMode_5480_ = lean_ctor_get(v_toEnvExtension_5479_, 2);
lean_inc(v_asyncMode_5480_);
lean_dec_ref(v_toEnvExtension_5479_);
v___x_5481_ = lean_box(0);
v___x_5482_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5474_, v___x_5478_, v_____do__lift_5477_, v_asyncMode_5480_, v___x_5481_);
lean_dec(v_asyncMode_5480_);
v_defaultInstances_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_defaultInstances_5483_);
lean_dec(v___x_5482_);
v___x_5484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5483_, v_className_5475_);
lean_dec(v_defaultInstances_5483_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5485_ = lean_box(0);
v___x_5486_ = lean_apply_2(v_toPure_5476_, lean_box(0), v___x_5485_);
return v___x_5486_;
}
else
{
lean_object* v_val_5487_; lean_object* v___x_5488_; 
v_val_5487_ = lean_ctor_get(v___x_5484_, 0);
lean_inc(v_val_5487_);
lean_dec_ref(v___x_5484_);
v___x_5488_ = lean_apply_2(v_toPure_5476_, lean_box(0), v_val_5487_);
return v___x_5488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5489_, lean_object* v_className_5490_, lean_object* v_toPure_5491_, lean_object* v_____do__lift_5492_){
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5489_, v_className_5490_, v_toPure_5491_, v_____do__lift_5492_);
lean_dec(v_className_5490_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5494_, lean_object* v_inst_5495_, lean_object* v_className_5496_){
_start:
{
lean_object* v_toApplicative_5497_; lean_object* v_toBind_5498_; lean_object* v_getEnv_5499_; lean_object* v_toPure_5500_; lean_object* v___x_5501_; lean_object* v___f_5502_; lean_object* v___x_5503_; 
v_toApplicative_5497_ = lean_ctor_get(v_inst_5494_, 0);
lean_inc_ref(v_toApplicative_5497_);
v_toBind_5498_ = lean_ctor_get(v_inst_5494_, 1);
lean_inc(v_toBind_5498_);
lean_dec_ref(v_inst_5494_);
v_getEnv_5499_ = lean_ctor_get(v_inst_5495_, 0);
lean_inc(v_getEnv_5499_);
lean_dec_ref(v_inst_5495_);
v_toPure_5500_ = lean_ctor_get(v_toApplicative_5497_, 1);
lean_inc(v_toPure_5500_);
lean_dec_ref(v_toApplicative_5497_);
v___x_5501_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5502_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5502_, 0, v___x_5501_);
lean_closure_set(v___f_5502_, 1, v_className_5496_);
lean_closure_set(v___f_5502_, 2, v_toPure_5500_);
v___x_5503_ = lean_apply_4(v_toBind_5498_, lean_box(0), lean_box(0), v_getEnv_5499_, v___f_5502_);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5504_, lean_object* v_inst_5505_, lean_object* v_inst_5506_, lean_object* v_className_5507_){
_start:
{
lean_object* v___x_5508_; 
v___x_5508_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5505_, v_inst_5506_, v_className_5507_);
return v___x_5508_;
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
