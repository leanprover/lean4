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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_519_; 
v_es_498_ = lean_ctor_get(v_x_495_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_519_ == 0)
{
v___x_500_ = v_x_495_;
v_isShared_501_ = v_isSharedCheck_519_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_es_498_);
lean_dec(v_x_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_519_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v_j_506_; lean_object* v___x_507_; 
v___x_502_ = lean_box(2);
v___x_503_ = ((size_t)5ULL);
v___x_504_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_505_ = lean_usize_land(v_x_496_, v___x_504_);
v_j_506_ = lean_usize_to_nat(v___x_505_);
v___x_507_ = lean_array_get(v___x_502_, v_es_498_, v_j_506_);
lean_dec(v_j_506_);
lean_dec_ref(v_es_498_);
switch(lean_obj_tag(v___x_507_))
{
case 0:
{
lean_object* v_key_508_; lean_object* v_val_509_; uint8_t v___x_510_; 
v_key_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_key_508_);
v_val_509_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_val_509_);
lean_dec_ref(v___x_507_);
v___x_510_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_497_, v_key_508_);
lean_dec(v_key_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v_val_509_);
lean_del_object(v___x_500_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v___x_513_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 1);
lean_ctor_set(v___x_500_, 0, v_val_509_);
v___x_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_val_509_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
case 1:
{
lean_object* v_node_515_; size_t v___x_516_; 
lean_del_object(v___x_500_);
v_node_515_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_node_515_);
lean_dec_ref(v___x_507_);
v___x_516_ = lean_usize_shift_right(v_x_496_, v___x_503_);
v_x_495_ = v_node_515_;
v_x_496_ = v___x_516_;
goto _start;
}
default: 
{
lean_object* v___x_518_; 
lean_del_object(v___x_500_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
}
}
}
else
{
lean_object* v_ks_520_; lean_object* v_vs_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_ks_520_ = lean_ctor_get(v_x_495_, 0);
lean_inc_ref(v_ks_520_);
v_vs_521_ = lean_ctor_get(v_x_495_, 1);
lean_inc_ref(v_vs_521_);
lean_dec_ref(v_x_495_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_520_, v_vs_521_, v___x_522_, v_x_497_);
lean_dec_ref(v_vs_521_);
lean_dec_ref(v_ks_520_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
size_t v_x_2529__boxed_527_; lean_object* v_res_528_; 
v_x_2529__boxed_527_ = lean_unbox_usize(v_x_525_);
lean_dec(v_x_525_);
v_res_528_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_524_, v_x_2529__boxed_527_, v_x_526_);
lean_dec(v_x_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint64_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_530_);
v___x_532_ = lean_uint64_to_usize(v___x_531_);
v___x_533_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_529_, v___x_532_, v_x_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_534_, v_x_535_);
lean_dec(v_x_535_);
return v_res_536_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(lean_object* v_msg_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3___closed__0);
v___x_540_ = lean_panic_fn_borrowed(v___x_539_, v_msg_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_570_; 
v_ks_545_ = lean_ctor_get(v_x_541_, 0);
v_vs_546_ = lean_ctor_get(v_x_541_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_570_ == 0)
{
v___x_548_ = v_x_541_;
v_isShared_549_ = v_isSharedCheck_570_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_vs_546_);
lean_inc(v_ks_545_);
lean_dec(v_x_541_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_570_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_array_get_size(v_ks_545_);
v___x_551_ = lean_nat_dec_lt(v_x_542_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
lean_dec(v_x_542_);
v___x_552_ = lean_array_push(v_ks_545_, v_x_543_);
v___x_553_ = lean_array_push(v_vs_546_, v_x_544_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_553_);
lean_ctor_set(v___x_548_, 0, v___x_552_);
v___x_555_ = v___x_548_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
lean_object* v_k_x27_557_; uint8_t v___x_558_; 
v_k_x27_557_ = lean_array_fget_borrowed(v_ks_545_, v_x_542_);
v___x_558_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_543_, v_k_x27_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_560_; 
if (v_isShared_549_ == 0)
{
v___x_560_ = v___x_548_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_ks_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_vs_546_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_add(v_x_542_, v___x_561_);
lean_dec(v_x_542_);
v_x_541_ = v___x_560_;
v_x_542_ = v___x_562_;
goto _start;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = lean_array_fset(v_ks_545_, v_x_542_, v_x_543_);
v___x_566_ = lean_array_fset(v_vs_546_, v_x_542_, v_x_544_);
lean_dec(v_x_542_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_566_);
lean_ctor_set(v___x_548_, 0, v___x_565_);
v___x_568_ = v___x_548_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_n_571_, lean_object* v_k_572_, lean_object* v_v_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_n_571_, v___x_574_, v_k_572_, v_v_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_x_577_, size_t v_x_578_, size_t v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v_es_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v_j_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_es_582_ = lean_ctor_get(v_x_577_, 0);
v___x_583_ = ((size_t)5ULL);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_586_ = lean_usize_land(v_x_578_, v___x_585_);
v_j_587_ = lean_usize_to_nat(v___x_586_);
v___x_588_ = lean_array_get_size(v_es_582_);
v___x_589_ = lean_nat_dec_lt(v_j_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v_j_587_);
lean_dec(v_x_581_);
lean_dec(v_x_580_);
return v_x_577_;
}
else
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_626_; 
lean_inc_ref(v_es_582_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_x_577_, 0);
lean_dec(v_unused_627_);
v___x_591_ = v_x_577_;
v_isShared_592_ = v_isSharedCheck_626_;
goto v_resetjp_590_;
}
else
{
lean_dec(v_x_577_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_626_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_v_593_; lean_object* v___x_594_; lean_object* v_xs_x27_595_; lean_object* v___y_597_; 
v_v_593_ = lean_array_fget(v_es_582_, v_j_587_);
v___x_594_ = lean_box(0);
v_xs_x27_595_ = lean_array_fset(v_es_582_, v_j_587_, v___x_594_);
switch(lean_obj_tag(v_v_593_))
{
case 0:
{
lean_object* v_key_602_; lean_object* v_val_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_613_; 
v_key_602_ = lean_ctor_get(v_v_593_, 0);
v_val_603_ = lean_ctor_get(v_v_593_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_v_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_605_ = v_v_593_;
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_val_603_);
lean_inc(v_key_602_);
lean_dec(v_v_593_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_580_, v_key_602_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_del_object(v___x_605_);
v___x_608_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_602_, v_val_603_, v_x_580_, v_x_581_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___y_597_ = v___x_609_;
goto v___jp_596_;
}
else
{
lean_object* v___x_611_; 
lean_dec(v_val_603_);
lean_dec(v_key_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v_x_581_);
lean_ctor_set(v___x_605_, 0, v_x_580_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_x_580_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_x_581_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v___y_597_ = v___x_611_;
goto v___jp_596_;
}
}
}
}
case 1:
{
lean_object* v_node_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_624_; 
v_node_614_ = lean_ctor_get(v_v_593_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_v_593_);
if (v_isSharedCheck_624_ == 0)
{
v___x_616_ = v_v_593_;
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_node_614_);
lean_dec(v_v_593_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_618_ = lean_usize_shift_right(v_x_578_, v___x_583_);
v___x_619_ = lean_usize_add(v_x_579_, v___x_584_);
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_node_614_, v___x_618_, v___x_619_, v_x_580_, v_x_581_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_620_);
v___x_622_ = v___x_616_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
v___y_597_ = v___x_622_;
goto v___jp_596_;
}
}
}
default: 
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_x_580_);
lean_ctor_set(v___x_625_, 1, v_x_581_);
v___y_597_ = v___x_625_;
goto v___jp_596_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_array_fset(v_xs_x27_595_, v_j_587_, v___y_597_);
lean_dec(v_j_587_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_600_ = v___x_591_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v_ks_628_; lean_object* v_vs_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_649_; 
v_ks_628_ = lean_ctor_get(v_x_577_, 0);
v_vs_629_ = lean_ctor_get(v_x_577_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_649_ == 0)
{
v___x_631_ = v_x_577_;
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_vs_629_);
lean_inc(v_ks_628_);
lean_dec(v_x_577_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_ks_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_vs_629_);
v___x_634_ = v_reuseFailAlloc_648_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v_newNode_635_; uint8_t v___y_637_; size_t v___x_643_; uint8_t v___x_644_; 
v_newNode_635_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v___x_634_, v_x_580_, v_x_581_);
v___x_643_ = ((size_t)7ULL);
v___x_644_ = lean_usize_dec_le(v___x_643_, v_x_579_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_635_);
v___x_646_ = lean_unsigned_to_nat(4u);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
lean_dec(v___x_645_);
v___y_637_ = v___x_647_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
lean_object* v_ks_638_; lean_object* v_vs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_ks_638_ = lean_ctor_get(v_newNode_635_, 0);
lean_inc_ref(v_ks_638_);
v_vs_639_ = lean_ctor_get(v_newNode_635_, 1);
lean_inc_ref(v_vs_639_);
lean_dec_ref(v_newNode_635_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_x_579_, v_ks_638_, v_vs_639_, v___x_640_, v___x_641_);
lean_dec_ref(v_vs_639_);
lean_dec_ref(v_ks_638_);
return v___x_642_;
}
else
{
return v_newNode_635_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(size_t v_depth_650_, lean_object* v_keys_651_, lean_object* v_vals_652_, lean_object* v_i_653_, lean_object* v_entries_654_){
_start:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_array_get_size(v_keys_651_);
v___x_656_ = lean_nat_dec_lt(v_i_653_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec(v_i_653_);
return v_entries_654_;
}
else
{
lean_object* v_k_657_; lean_object* v_v_658_; uint64_t v___x_659_; size_t v_h_660_; size_t v___x_661_; lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v_h_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_k_657_ = lean_array_fget_borrowed(v_keys_651_, v_i_653_);
v_v_658_ = lean_array_fget_borrowed(v_vals_652_, v_i_653_);
v___x_659_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_657_);
v_h_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = ((size_t)5ULL);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v_depth_650_, v___x_663_);
v___x_665_ = lean_usize_mul(v___x_661_, v___x_664_);
v_h_666_ = lean_usize_shift_right(v_h_660_, v___x_665_);
v___x_667_ = lean_nat_add(v_i_653_, v___x_662_);
lean_dec(v_i_653_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v___x_668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_entries_654_, v_h_666_, v_depth_650_, v_k_657_, v_v_658_);
v_i_653_ = v___x_667_;
v_entries_654_ = v___x_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_670_, lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_i_673_, lean_object* v_entries_674_){
_start:
{
size_t v_depth_boxed_675_; lean_object* v_res_676_; 
v_depth_boxed_675_ = lean_unbox_usize(v_depth_670_);
lean_dec(v_depth_670_);
v_res_676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_boxed_675_, v_keys_671_, v_vals_672_, v_i_673_, v_entries_674_);
lean_dec_ref(v_vals_672_);
lean_dec_ref(v_keys_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
size_t v_x_2691__boxed_682_; size_t v_x_2692__boxed_683_; lean_object* v_res_684_; 
v_x_2691__boxed_682_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_x_2692__boxed_683_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_677_, v_x_2691__boxed_682_, v_x_2692__boxed_683_, v_x_680_, v_x_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
uint64_t v___x_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___x_688_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_686_);
v___x_689_ = lean_uint64_to_usize(v___x_688_);
v___x_690_ = ((size_t)1ULL);
v___x_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_685_, v___x_689_, v___x_690_, v_x_686_, v_x_687_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_696_ = lean_unsigned_to_nat(23u);
v___x_697_ = lean_unsigned_to_nat(166u);
v___x_698_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_699_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_700_ = l_mkPanicMessageWithDecl(v___x_699_, v___x_698_, v___x_697_, v___x_696_, v___x_695_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_701_, lean_object* v_keys_702_, lean_object* v_v_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_array_get_size(v_keys_702_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_nat_dec_eq(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v_k_708_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
v_k_708_ = lean_array_get_borrowed(v___x_707_, v_keys_702_, v___x_705_);
lean_inc_ref(v_d_701_);
v___x_709_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_d_701_, v_k_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; lean_object* v_c_711_; lean_object* v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v_c_711_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_702_, v_v_703_, v___x_710_);
lean_inc(v_k_708_);
v___x_712_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_701_, v_k_708_, v_c_711_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v_c_715_; lean_object* v___x_716_; 
v_val_713_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v___x_709_);
v___x_714_ = lean_unsigned_to_nat(1u);
v_c_715_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v_keys_702_, v_v_703_, v___x_714_, v_val_713_);
lean_inc(v_k_708_);
v___x_716_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_d_701_, v_k_708_, v_c_715_);
return v___x_716_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec_ref(v_v_703_);
lean_dec_ref(v_d_701_);
v___x_717_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_718_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__3(v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_719_, lean_object* v_keys_720_, lean_object* v_v_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_719_, v_keys_720_, v_v_721_);
lean_dec_ref(v_keys_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(lean_object* v_xs_723_, lean_object* v_v_724_, lean_object* v_i_725_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_array_get_size(v_xs_723_);
v___x_727_ = lean_nat_dec_lt(v_i_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_i_725_);
v___x_728_ = lean_box(0);
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_fget_borrowed(v_xs_723_, v_i_725_);
v___x_730_ = lean_name_eq(v___x_729_, v_v_724_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_i_725_, v___x_731_);
lean_dec(v_i_725_);
v_i_725_ = v___x_732_;
goto _start;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_i_725_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21___boxed(lean_object* v_xs_735_, lean_object* v_v_736_, lean_object* v_i_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_735_, v_v_736_, v_i_737_);
lean_dec(v_v_736_);
lean_dec_ref(v_xs_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(lean_object* v_xs_739_, lean_object* v_v_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14_spec__21(v_xs_739_, v_v_740_, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14___boxed(lean_object* v_xs_743_, lean_object* v_v_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_xs_743_, v_v_744_);
lean_dec(v_v_744_);
lean_dec_ref(v_xs_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(lean_object* v_x_746_, size_t v_x_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v_es_749_; lean_object* v___x_750_; size_t v___x_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v_j_754_; lean_object* v_entry_755_; 
v_es_749_ = lean_ctor_get(v_x_746_, 0);
v___x_750_ = lean_box(2);
v___x_751_ = ((size_t)5ULL);
v___x_752_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_753_ = lean_usize_land(v_x_747_, v___x_752_);
v_j_754_ = lean_usize_to_nat(v___x_753_);
v_entry_755_ = lean_array_get(v___x_750_, v_es_749_, v_j_754_);
switch(lean_obj_tag(v_entry_755_))
{
case 0:
{
lean_object* v_key_756_; uint8_t v___x_757_; 
v_key_756_ = lean_ctor_get(v_entry_755_, 0);
lean_inc(v_key_756_);
lean_dec_ref(v_entry_755_);
v___x_757_ = lean_name_eq(v_x_748_, v_key_756_);
lean_dec(v_key_756_);
if (v___x_757_ == 0)
{
lean_dec(v_j_754_);
return v_x_746_;
}
else
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
lean_inc_ref(v_es_749_);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_x_746_, 0);
lean_dec(v_unused_766_);
v___x_759_ = v_x_746_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_x_746_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_array_set(v_es_749_, v_j_754_, v___x_750_);
lean_dec(v_j_754_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
case 1:
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_800_; 
lean_inc_ref(v_es_749_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_x_746_, 0);
lean_dec(v_unused_801_);
v___x_768_ = v_x_746_;
v_isShared_769_ = v_isSharedCheck_800_;
goto v_resetjp_767_;
}
else
{
lean_dec(v_x_746_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_800_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_node_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_799_; 
v_node_770_ = lean_ctor_get(v_entry_755_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_entry_755_);
if (v_isSharedCheck_799_ == 0)
{
v___x_772_ = v_entry_755_;
v_isShared_773_ = v_isSharedCheck_799_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_node_770_);
lean_dec(v_entry_755_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_799_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_entries_774_; size_t v___x_775_; lean_object* v_newNode_776_; lean_object* v___x_777_; 
v_entries_774_ = lean_array_set(v_es_749_, v_j_754_, v___x_750_);
v___x_775_ = lean_usize_shift_right(v_x_747_, v___x_751_);
v_newNode_776_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_node_770_, v___x_775_, v_x_748_);
lean_inc_ref(v_newNode_776_);
v___x_777_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_779_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_newNode_776_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_newNode_776_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_array_set(v_entries_774_, v_j_754_, v___x_779_);
lean_dec(v_j_754_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_780_);
v___x_782_ = v___x_768_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_val_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_newNode_776_);
lean_del_object(v___x_772_);
v_val_785_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_785_);
lean_dec_ref(v___x_777_);
v_fst_786_ = lean_ctor_get(v_val_785_, 0);
v_snd_787_ = lean_ctor_get(v_val_785_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_val_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_789_ = v_val_785_;
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_786_);
lean_dec(v_val_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_fst_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_snd_787_);
v___x_792_ = v_reuseFailAlloc_797_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_array_set(v_entries_774_, v_j_754_, v___x_792_);
lean_dec(v_j_754_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_793_);
v___x_795_ = v___x_768_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_754_);
return v_x_746_;
}
}
}
else
{
lean_object* v_ks_802_; lean_object* v_vs_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_ks_802_ = lean_ctor_get(v_x_746_, 0);
v_vs_803_ = lean_ctor_get(v_x_746_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_817_ == 0)
{
v___x_805_ = v_x_746_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_vs_803_);
lean_inc(v_ks_802_);
lean_dec(v_x_746_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; 
v___x_807_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7_spec__14(v_ks_802_, v_x_748_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_809_; 
if (v_isShared_806_ == 0)
{
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_ks_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_vs_803_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v_val_811_; lean_object* v_keys_x27_812_; lean_object* v_vals_x27_813_; lean_object* v___x_815_; 
v_val_811_ = lean_ctor_get(v___x_807_, 0);
lean_inc_n(v_val_811_, 2);
lean_dec_ref(v___x_807_);
v_keys_x27_812_ = l_Array_eraseIdx___redArg(v_ks_802_, v_val_811_);
v_vals_x27_813_ = l_Array_eraseIdx___redArg(v_vs_803_, v_val_811_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_vals_x27_813_);
lean_ctor_set(v___x_805_, 0, v_keys_x27_812_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_keys_x27_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_vals_x27_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
size_t v_x_2940__boxed_821_; lean_object* v_res_822_; 
v_x_2940__boxed_821_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_res_822_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_818_, v_x_2940__boxed_821_, v_x_820_);
lean_dec(v_x_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
uint64_t v___y_826_; 
if (lean_obj_tag(v_x_824_) == 0)
{
uint64_t v___x_829_; 
v___x_829_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_826_ = v___x_829_;
goto v___jp_825_;
}
else
{
uint64_t v_hash_830_; 
v_hash_830_ = lean_ctor_get_uint64(v_x_824_, sizeof(void*)*2);
v___y_826_ = v_hash_830_;
goto v___jp_825_;
}
v___jp_825_:
{
size_t v_h_827_; lean_object* v___x_828_; 
v_h_827_ = lean_uint64_to_usize(v___y_826_);
v___x_828_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_823_, v_h_827_, v_x_824_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_831_, v_x_832_);
lean_dec(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_834_, lean_object* v_e_835_){
_start:
{
lean_object* v_globalName_x3f_836_; 
v_globalName_x3f_836_ = lean_ctor_get(v_e_835_, 3);
if (lean_obj_tag(v_globalName_x3f_836_) == 0)
{
lean_object* v_keys_837_; lean_object* v_discrTree_838_; lean_object* v_instanceNames_839_; lean_object* v_erased_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_keys_837_ = lean_ctor_get(v_e_835_, 0);
lean_inc_ref(v_keys_837_);
v_discrTree_838_ = lean_ctor_get(v_d_834_, 0);
v_instanceNames_839_ = lean_ctor_get(v_d_834_, 1);
v_erased_840_ = lean_ctor_get(v_d_834_, 2);
v_isSharedCheck_848_ = !lean_is_exclusive(v_d_834_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v_d_834_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_erased_840_);
lean_inc(v_instanceNames_839_);
lean_inc(v_discrTree_838_);
lean_dec(v_d_834_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_838_, v_keys_837_, v_e_835_);
lean_dec_ref(v_keys_837_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_instanceNames_839_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_erased_840_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_keys_849_; lean_object* v_val_850_; lean_object* v_discrTree_851_; lean_object* v_instanceNames_852_; lean_object* v_erased_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
v_keys_849_ = lean_ctor_get(v_e_835_, 0);
v_val_850_ = lean_ctor_get(v_globalName_x3f_836_, 0);
lean_inc(v_val_850_);
v_discrTree_851_ = lean_ctor_get(v_d_834_, 0);
v_instanceNames_852_ = lean_ctor_get(v_d_834_, 1);
v_erased_853_ = lean_ctor_get(v_d_834_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_d_834_);
if (v_isSharedCheck_863_ == 0)
{
v___x_855_ = v_d_834_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_erased_853_);
lean_inc(v_instanceNames_852_);
lean_inc(v_discrTree_851_);
lean_dec(v_d_834_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_inc_ref(v_e_835_);
v___x_857_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_851_, v_keys_849_, v_e_835_);
lean_inc(v_val_850_);
v___x_858_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_852_, v_val_850_, v_e_835_);
v___x_859_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_853_, v_val_850_);
lean_dec(v_val_850_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 2, v___x_859_);
lean_ctor_set(v___x_855_, 1, v___x_858_);
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_865_, v_x_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_873_, v_x_874_, v_x_875_);
lean_dec(v_x_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_00_u03b2_881_, v_x_882_, v_x_883_);
lean_dec(v_x_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___redArg(v_x_886_, v_x_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(lean_object* v_00_u03b2_890_, lean_object* v_x_891_, size_t v_x_892_, size_t v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg(v_x_891_, v_x_892_, v_x_893_, v_x_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___boxed(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
size_t v_x_3165__boxed_903_; size_t v_x_3166__boxed_904_; lean_object* v_res_905_; 
v_x_3165__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_x_3166__boxed_904_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5(v_00_u03b2_897_, v_x_898_, v_x_3165__boxed_903_, v_x_3166__boxed_904_, v_x_901_, v_x_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___redArg(v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7___boxed(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
size_t v_x_3182__boxed_915_; lean_object* v_res_916_; 
v_x_3182__boxed_915_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_916_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__7(v_00_u03b2_911_, v_x_912_, v_x_3182__boxed_915_, v_x_914_);
lean_dec(v_x_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_917_, lean_object* v_x_918_, size_t v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___redArg(v_x_918_, v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
size_t v_x_3193__boxed_926_; lean_object* v_res_927_; 
v_x_3193__boxed_926_ = lean_unbox_usize(v_x_924_);
lean_dec(v_x_924_);
v_res_927_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_00_u03b2_922_, v_x_923_, v_x_3193__boxed_926_, v_x_925_);
lean_dec(v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_928_, lean_object* v_x_929_, size_t v_x_930_, size_t v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___redArg(v_x_929_, v_x_930_, v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_3204__boxed_941_; size_t v_x_3205__boxed_942_; lean_object* v_res_943_; 
v_x_3204__boxed_941_ = lean_unbox_usize(v_x_937_);
lean_dec(v_x_937_);
v_x_3205__boxed_942_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_res_943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3(v_00_u03b2_935_, v_x_936_, v_x_3204__boxed_941_, v_x_3205__boxed_942_, v_x_939_, v_x_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_944_, lean_object* v_n_945_, lean_object* v_k_946_, lean_object* v_v_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10___redArg(v_n_945_, v_k_946_, v_v_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_949_, size_t v_depth_950_, lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_heq_953_, lean_object* v_i_954_, lean_object* v_entries_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg(v_depth_950_, v_keys_951_, v_vals_952_, v_i_954_, v_entries_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_957_, lean_object* v_depth_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_heq_961_, lean_object* v_i_962_, lean_object* v_entries_963_){
_start:
{
size_t v_depth_boxed_964_; lean_object* v_res_965_; 
v_depth_boxed_964_ = lean_unbox_usize(v_depth_958_);
lean_dec(v_depth_958_);
v_res_965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11(v_00_u03b2_957_, v_depth_boxed_964_, v_keys_959_, v_vals_960_, v_heq_961_, v_i_962_, v_entries_963_);
lean_dec_ref(v_vals_960_);
lean_dec_ref(v_keys_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_966_, lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_heq_969_, lean_object* v_i_970_, lean_object* v_k_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_967_, v_vals_968_, v_i_970_, v_k_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_973_, lean_object* v_keys_974_, lean_object* v_vals_975_, lean_object* v_heq_976_, lean_object* v_i_977_, lean_object* v_k_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_973_, v_keys_974_, v_vals_975_, v_heq_976_, v_i_977_, v_k_978_);
lean_dec(v_k_978_);
lean_dec_ref(v_vals_975_);
lean_dec_ref(v_keys_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_980_, lean_object* v_n_981_, lean_object* v_k_982_, lean_object* v_v_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8___redArg(v_n_981_, v_k_982_, v_v_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_985_, size_t v_depth_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_entries_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___redArg(v_depth_986_, v_keys_987_, v_vals_988_, v_i_990_, v_entries_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_993_, lean_object* v_depth_994_, lean_object* v_keys_995_, lean_object* v_vals_996_, lean_object* v_heq_997_, lean_object* v_i_998_, lean_object* v_entries_999_){
_start:
{
size_t v_depth_boxed_1000_; lean_object* v_res_1001_; 
v_depth_boxed_1000_ = lean_unbox_usize(v_depth_994_);
lean_dec(v_depth_994_);
v_res_1001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_993_, v_depth_boxed_1000_, v_keys_995_, v_vals_996_, v_heq_997_, v_i_998_, v_entries_999_);
lean_dec_ref(v_vals_996_);
lean_dec_ref(v_keys_995_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(lean_object* v_x_1002_, lean_object* v_keys_1003_, lean_object* v_v_1004_, lean_object* v_k_1005_, lean_object* v_as_1006_, lean_object* v_k_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___redArg(v_x_1002_, v_keys_1003_, v_v_1004_, v_k_1005_, v_as_1006_, v_k_1007_, v_x_1008_, v_x_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14___boxed(lean_object* v_x_1013_, lean_object* v_keys_1014_, lean_object* v_v_1015_, lean_object* v_k_1016_, lean_object* v_as_1017_, lean_object* v_k_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2_spec__6_spec__14(v_x_1013_, v_keys_1014_, v_v_1015_, v_k_1016_, v_as_1017_, v_k_1018_, v_x_1019_, v_x_1020_, v_x_1021_, v_x_1022_);
lean_dec_ref(v_k_1018_);
lean_dec_ref(v_keys_1014_);
lean_dec(v_x_1013_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17(lean_object* v_00_u03b2_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__10_spec__17___redArg(v_x_1025_, v_x_1026_, v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_1031_, v_x_1032_, v_x_1033_, v_x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1036_, lean_object* v_declName_1037_){
_start:
{
lean_object* v_discrTree_1038_; lean_object* v_instanceNames_1039_; lean_object* v_erased_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1050_; 
v_discrTree_1038_ = lean_ctor_get(v_d_1036_, 0);
v_instanceNames_1039_ = lean_ctor_get(v_d_1036_, 1);
v_erased_1040_ = lean_ctor_get(v_d_1036_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_d_1036_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1042_ = v_d_1036_;
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_erased_1040_);
lean_inc(v_instanceNames_1039_);
lean_inc(v_discrTree_1038_);
lean_dec(v_d_1036_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1044_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1039_, v_declName_1037_);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1040_, v_declName_1037_, v___x_1045_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 2, v___x_1046_);
lean_ctor_set(v___x_1042_, 1, v___x_1044_);
v___x_1048_ = v___x_1042_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_discrTree_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1051_, lean_object* v_declName_1052_, lean_object* v_toPure_1053_, lean_object* v_____r_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = l_Lean_Meta_Instances_eraseCore(v_d_1051_, v_declName_1052_);
v___x_1056_ = lean_apply_2(v_toPure_1053_, lean_box(0), v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1057_, lean_object* v_____r_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_apply_1(v___f_1057_, v_____r_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_d_1070_, lean_object* v_declName_1071_){
_start:
{
lean_object* v_toApplicative_1072_; lean_object* v_toBind_1073_; lean_object* v_toPure_1074_; lean_object* v_instanceNames_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; uint8_t v___x_1079_; 
v_toApplicative_1072_ = lean_ctor_get(v_inst_1068_, 0);
v_toBind_1073_ = lean_ctor_get(v_inst_1068_, 1);
lean_inc(v_toBind_1073_);
v_toPure_1074_ = lean_ctor_get(v_toApplicative_1072_, 1);
v_instanceNames_1075_ = lean_ctor_get(v_d_1070_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1077_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1074_);
lean_inc_n(v_declName_1071_, 2);
lean_inc_ref(v_d_1070_);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1078_, 0, v_d_1070_);
lean_closure_set(v___f_1078_, 1, v_declName_1071_);
lean_closure_set(v___f_1078_, 2, v_toPure_1074_);
lean_inc_ref(v_instanceNames_1075_);
v___x_1079_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1076_, v___x_1077_, v_instanceNames_1075_, v_declName_1071_);
if (v___x_1079_ == 0)
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v_d_1070_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1080_, 0, v___f_1078_);
v___x_1081_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1082_ = l_Lean_MessageData_ofConstName(v_declName_1071_, v___x_1079_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_throwError___redArg(v_inst_1068_, v_inst_1069_, v___x_1085_);
v___x_1087_ = lean_apply_4(v_toBind_1073_, lean_box(0), lean_box(0), v___x_1086_, v___f_1080_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc(v_toPure_1074_);
lean_dec_ref(v___f_1078_);
lean_dec(v_toBind_1073_);
lean_dec_ref(v_inst_1069_);
lean_dec_ref(v_inst_1068_);
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1070_, v_declName_1071_, v_toPure_1074_, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_d_1093_, lean_object* v_declName_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1091_, v_inst_1092_, v_d_1093_, v_declName_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(uint8_t v_level_1096_, lean_object* v_e_1097_){
_start:
{
uint8_t v___y_1099_; uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 2;
v___x_1103_ = l_Lean_instDecidableEqOLeanLevel(v_level_1096_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_globalName_x3f_1104_; 
v_globalName_x3f_1104_ = lean_ctor_get(v_e_1097_, 3);
lean_inc(v_globalName_x3f_1104_);
if (lean_obj_tag(v_globalName_x3f_1104_) == 0)
{
v___y_1099_ = v___x_1103_;
goto v___jp_1098_;
}
else
{
lean_object* v_val_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_val_1105_ = lean_ctor_get(v_globalName_x3f_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_globalName_x3f_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v_globalName_x3f_1104_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_val_1105_);
lean_dec(v_globalName_x3f_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_isPrivateName(v_val_1105_);
lean_dec(v_val_1105_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v_e_1097_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_e_1097_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_del_object(v___x_1107_);
v___y_1099_ = v___x_1103_;
goto v___jp_1098_;
}
}
}
}
else
{
v___y_1099_ = v___x_1103_;
goto v___jp_1098_;
}
v___jp_1098_:
{
if (v___y_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v_e_1097_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_e_1097_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_level_1114_, lean_object* v_e_1115_){
_start:
{
uint8_t v_level_boxed_1116_; lean_object* v_res_1117_; 
v_level_boxed_1116_ = lean_unbox(v_level_1114_);
v_res_1117_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v_level_boxed_1116_, v_e_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(lean_object* v___y_1118_){
_start:
{
lean_inc_ref(v___y_1118_);
return v___y_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(v___y_1119_);
lean_dec_ref(v___y_1119_);
return v_res_1120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___f_1129_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___f_1130_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1131_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_));
v___x_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
lean_ctor_set(v___x_1134_, 2, v___x_1131_);
lean_ctor_set(v___x_1134_, 3, v___f_1130_);
lean_ctor_set(v___x_1134_, 4, v___f_1129_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_);
v___x_1137_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2____boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2480378690____hygCtx___hyg_2_();
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1140_, uint8_t v_allowLevelAssignments_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1141_, v_k_1140_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
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
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1164_, lean_object* v_allowLevelAssignments_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1171_; lean_object* v_res_1172_; 
v_allowLevelAssignments_boxed_1171_ = lean_unbox(v_allowLevelAssignments_1165_);
v_res_1172_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1164_, v_allowLevelAssignments_boxed_1171_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1173_, lean_object* v_k_1174_, uint8_t v_allowLevelAssignments_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1174_, v_allowLevelAssignments_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_k_1183_, lean_object* v_allowLevelAssignments_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1190_; lean_object* v_res_1191_; 
v_allowLevelAssignments_boxed_1190_ = lean_unbox(v_allowLevelAssignments_1184_);
v_res_1191_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1182_, v_k_1183_, v_allowLevelAssignments_boxed_1190_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1192_, lean_object* v___x_1193_, uint8_t v___x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1192_, v___x_1193_, v___x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_snd_1202_; lean_object* v_snd_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
v_snd_1202_ = lean_ctor_get(v_a_1201_, 1);
lean_inc(v_snd_1202_);
lean_dec(v_a_1201_);
v_snd_1203_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_snd_1203_);
lean_dec(v_snd_1202_);
v___x_1204_ = 0;
v___x_1205_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1203_, v___x_1204_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1200_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1200_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v___x_497__boxed_1222_; lean_object* v_res_1223_; 
v___x_497__boxed_1222_ = lean_unbox(v___x_1216_);
v_res_1223_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1214_, v___x_1215_, v___x_497__boxed_1222_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
lean_inc(v_a_1228_);
lean_inc_ref(v_a_1227_);
lean_inc(v_a_1226_);
lean_inc_ref(v_a_1225_);
v___x_1230_ = lean_infer_type(v_e_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = lean_box(0);
v___x_1233_ = 0;
v___x_1234_ = lean_box(v___x_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1235_, 0, v_a_1231_);
lean_closure_set(v___f_1235_, 1, v___x_1232_);
lean_closure_set(v___f_1235_, 2, v___x_1234_);
v___x_1236_ = 0;
v___x_1237_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1235_, v___x_1236_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
return v___x_1237_;
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1230_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1230_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1253_, lean_object* v_b_1254_, lean_object* v_c_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1261_ = lean_apply_7(v_k_1253_, v_b_1254_, v_c_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, lean_box(0));
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1262_, lean_object* v_b_1263_, lean_object* v_c_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1262_, v_b_1263_, v_c_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1271_, lean_object* v_k_1272_, uint8_t v_cleanupAnnotations_1273_, uint8_t v_whnfType_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1280_, 0, v_k_1272_);
v___x_1281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1271_, v___f_1280_, v_cleanupAnnotations_1273_, v_whnfType_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
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
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1281_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1281_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1298_, lean_object* v_k_1299_, lean_object* v_cleanupAnnotations_1300_, lean_object* v_whnfType_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1307_; uint8_t v_whnfType_boxed_1308_; lean_object* v_res_1309_; 
v_cleanupAnnotations_boxed_1307_ = lean_unbox(v_cleanupAnnotations_1300_);
v_whnfType_boxed_1308_ = lean_unbox(v_whnfType_1301_);
v_res_1309_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1298_, v_k_1299_, v_cleanupAnnotations_boxed_1307_, v_whnfType_boxed_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1310_, lean_object* v_type_1311_, lean_object* v_k_1312_, uint8_t v_cleanupAnnotations_1313_, uint8_t v_whnfType_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1311_, v_k_1312_, v_cleanupAnnotations_1313_, v_whnfType_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_type_1322_, lean_object* v_k_1323_, lean_object* v_cleanupAnnotations_1324_, lean_object* v_whnfType_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; uint8_t v_whnfType_boxed_1332_; lean_object* v_res_1333_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1324_);
v_whnfType_boxed_1332_ = lean_unbox(v_whnfType_1325_);
v_res_1333_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1321_, v_type_1322_, v_k_1323_, v_cleanupAnnotations_boxed_1331_, v_whnfType_boxed_1332_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_b_1340_);
return v___x_1347_;
}
else
{
lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1401_; 
v_fst_1348_ = lean_ctor_get(v_b_1340_, 0);
v_snd_1349_ = lean_ctor_get(v_b_1340_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_b_1340_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1351_ = v_b_1340_;
v_isShared_1352_ = v_isSharedCheck_1401_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_snd_1349_);
lean_inc(v_fst_1348_);
lean_dec(v_b_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1401_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_next_1358_; 
v_next_1358_ = lean_ctor_get(v_snd_1349_, 0);
lean_inc(v_next_1358_);
if (lean_obj_tag(v_next_1358_) == 0)
{
goto v___jp_1353_;
}
else
{
lean_object* v_upperBound_1359_; lean_object* v_val_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1400_; 
v_upperBound_1359_ = lean_ctor_get(v_snd_1349_, 1);
v_val_1360_ = lean_ctor_get(v_next_1358_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_next_1358_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1362_ = v_next_1358_;
v_isShared_1363_ = v_isSharedCheck_1400_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_val_1360_);
lean_dec(v_next_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1400_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_nat_dec_lt(v_val_1360_, v_upperBound_1359_);
if (v___x_1364_ == 0)
{
lean_del_object(v___x_1362_);
lean_dec(v_val_1360_);
goto v___jp_1353_;
}
else
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1397_; 
lean_inc(v_upperBound_1359_);
lean_del_object(v___x_1351_);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_snd_1349_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1398_ = lean_ctor_get(v_snd_1349_, 1);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_snd_1349_, 0);
lean_dec(v_unused_1399_);
v___x_1366_ = v_snd_1349_;
v_isShared_1367_ = v_isSharedCheck_1397_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_snd_1349_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1397_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_array_uget_borrowed(v_as_1337_, v_i_1339_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v_a_1368_);
v___x_1369_ = lean_infer_type(v_a_1368_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_a_1372_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_val_1360_, v___x_1376_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1377_);
v___x_1379_ = v___x_1362_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1378_;
}
v___jp_1371_:
{
size_t v___x_1373_; size_t v___x_1374_; 
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_add(v_i_1339_, v___x_1373_);
v_i_1339_ = v___x_1374_;
v_b_1340_ = v_a_1372_;
goto _start;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1379_);
v___x_1381_ = v___x_1366_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_upperBound_1359_);
v___x_1381_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1383_ = l_Lean_Expr_isAppOf(v_a_1370_, v___x_1382_);
lean_dec(v_a_1370_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_val_1360_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_fst_1348_);
lean_ctor_set(v___x_1384_, 1, v___x_1381_);
v_a_1372_ = v___x_1384_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_array_push(v_fst_1348_, v_val_1360_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___x_1381_);
v_a_1372_ = v___x_1386_;
goto v___jp_1371_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_del_object(v___x_1366_);
lean_del_object(v___x_1362_);
lean_dec(v_val_1360_);
lean_dec(v_upperBound_1359_);
lean_dec(v_fst_1348_);
v_a_1389_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1369_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1369_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
v___jp_1353_:
{
lean_object* v___x_1355_; 
if (v_isShared_1352_ == 0)
{
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_fst_1348_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1349_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1402_, lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
size_t v_sz_boxed_1411_; size_t v_i_boxed_1412_; lean_object* v_res_1413_; 
v_sz_boxed_1411_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1412_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1402_, v_sz_boxed_1411_, v_i_boxed_1412_, v_b_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v_as_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1418_, lean_object* v_args_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v___y_1428_; lean_object* v_env_1453_; lean_object* v___x_1454_; 
v___x_1426_ = lean_st_ref_get(v___y_1424_);
v_env_1453_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_ref(v_env_1453_);
lean_dec(v___x_1426_);
v___x_1454_ = l_Lean_getOutParamPositions_x3f(v_env_1453_, v_declName_1418_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1428_ = v___x_1455_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1456_; 
v_val_1456_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1456_);
lean_dec_ref(v___x_1454_);
v___y_1428_ = v_val_1456_;
goto v___jp_1427_;
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1429_ = lean_array_get_size(v_args_1419_);
v___x_1430_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1428_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v_sz_1433_ = lean_array_size(v_args_1419_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1419_, v_sz_1433_, v___x_1434_, v___x_1432_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_fst_1440_; lean_object* v___x_1442_; 
v_fst_1440_ = lean_ctor_get(v_a_1436_, 0);
lean_inc(v_fst_1440_);
lean_dec(v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_fst_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_fst_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_a_1445_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1435_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1435_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1457_, lean_object* v_args_1458_, lean_object* v_x_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1457_, v_args_1458_, v_x_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec_ref(v_x_1459_);
lean_dec_ref(v_args_1458_);
lean_dec(v_declName_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Expr_getAppFn(v_classTy_1466_);
if (lean_obj_tag(v___x_1472_) == 4)
{
lean_object* v_declName_1473_; lean_object* v___x_1474_; 
v_declName_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_declName_1473_);
lean_inc(v_a_1470_);
lean_inc_ref(v_a_1469_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1474_ = lean_infer_type(v___x_1472_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___f_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
v___f_1476_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1476_, 0, v_declName_1473_);
v___x_1477_ = 0;
v___x_1478_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1475_, v___f_1476_, v___x_1477_, v___x_1477_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1478_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_declName_1473_);
v_a_1479_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1474_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1474_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v___x_1472_);
v___x_1487_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec_ref(v_classTy_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v_ks_1500_; lean_object* v_vs_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1525_; 
v_ks_1500_ = lean_ctor_get(v_x_1496_, 0);
v_vs_1501_ = lean_ctor_get(v_x_1496_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1496_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1503_ = v_x_1496_;
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_vs_1501_);
lean_inc(v_ks_1500_);
lean_dec(v_x_1496_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1525_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = lean_array_get_size(v_ks_1500_);
v___x_1506_ = lean_nat_dec_lt(v_x_1497_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_dec(v_x_1497_);
v___x_1507_ = lean_array_push(v_ks_1500_, v_x_1498_);
v___x_1508_ = lean_array_push(v_vs_1501_, v_x_1499_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1508_);
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1510_ = v___x_1503_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
else
{
lean_object* v_k_x27_1512_; uint8_t v___x_1513_; 
v_k_x27_1512_ = lean_array_fget_borrowed(v_ks_1500_, v_x_1497_);
v___x_1513_ = l_Lean_instBEqMVarId_beq(v_x_1498_, v_k_x27_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; 
if (v_isShared_1504_ == 0)
{
v___x_1515_ = v___x_1503_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_ks_1500_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_vs_1501_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_x_1497_, v___x_1516_);
lean_dec(v_x_1497_);
v_x_1496_ = v___x_1515_;
v_x_1497_ = v___x_1517_;
goto _start;
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_array_fset(v_ks_1500_, v_x_1497_, v_x_1498_);
v___x_1521_ = lean_array_fset(v_vs_1501_, v_x_1497_, v_x_1499_);
lean_dec(v_x_1497_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1521_);
lean_ctor_set(v___x_1503_, 0, v___x_1520_);
v___x_1523_ = v___x_1503_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_1526_, lean_object* v_k_1527_, lean_object* v_v_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_1526_, v___x_1529_, v_k_1527_, v_v_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1531_, size_t v_x_1532_, size_t v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v_es_1536_; size_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v_j_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_es_1536_ = lean_ctor_get(v_x_1531_, 0);
v___x_1537_ = ((size_t)5ULL);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_1540_ = lean_usize_land(v_x_1532_, v___x_1539_);
v_j_1541_ = lean_usize_to_nat(v___x_1540_);
v___x_1542_ = lean_array_get_size(v_es_1536_);
v___x_1543_ = lean_nat_dec_lt(v_j_1541_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_dec(v_j_1541_);
lean_dec(v_x_1535_);
lean_dec(v_x_1534_);
return v_x_1531_;
}
else
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1580_; 
lean_inc_ref(v_es_1536_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_x_1531_, 0);
lean_dec(v_unused_1581_);
v___x_1545_ = v_x_1531_;
v_isShared_1546_ = v_isSharedCheck_1580_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_x_1531_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1580_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_v_1547_; lean_object* v___x_1548_; lean_object* v_xs_x27_1549_; lean_object* v___y_1551_; 
v_v_1547_ = lean_array_fget(v_es_1536_, v_j_1541_);
v___x_1548_ = lean_box(0);
v_xs_x27_1549_ = lean_array_fset(v_es_1536_, v_j_1541_, v___x_1548_);
switch(lean_obj_tag(v_v_1547_))
{
case 0:
{
lean_object* v_key_1556_; lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
v_key_1556_ = lean_ctor_get(v_v_1547_, 0);
v_val_1557_ = lean_ctor_get(v_v_1547_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_v_1547_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1559_ = v_v_1547_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_inc(v_key_1556_);
lean_dec(v_v_1547_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_instBEqMVarId_beq(v_x_1534_, v_key_1556_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_del_object(v___x_1559_);
v___x_1562_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1556_, v_val_1557_, v_x_1534_, v_x_1535_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___y_1551_ = v___x_1563_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1565_; 
lean_dec(v_val_1557_);
lean_dec(v_key_1556_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v_x_1535_);
lean_ctor_set(v___x_1559_, 0, v_x_1534_);
v___x_1565_ = v___x_1559_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_x_1534_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_x_1535_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
v___y_1551_ = v___x_1565_;
goto v___jp_1550_;
}
}
}
}
case 1:
{
lean_object* v_node_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1578_; 
v_node_1568_ = lean_ctor_get(v_v_1547_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_v_1547_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1570_ = v_v_1547_;
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_node_1568_);
lean_dec(v_v_1547_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1572_ = lean_usize_shift_right(v_x_1532_, v___x_1537_);
v___x_1573_ = lean_usize_add(v_x_1533_, v___x_1538_);
v___x_1574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_node_1568_, v___x_1572_, v___x_1573_, v_x_1534_, v_x_1535_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1574_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
v___y_1551_ = v___x_1576_;
goto v___jp_1550_;
}
}
}
default: 
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_x_1534_);
lean_ctor_set(v___x_1579_, 1, v_x_1535_);
v___y_1551_ = v___x_1579_;
goto v___jp_1550_;
}
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_array_fset(v_xs_x27_1549_, v_j_1541_, v___y_1551_);
lean_dec(v_j_1541_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1552_);
v___x_1554_ = v___x_1545_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_object* v_ks_1582_; lean_object* v_vs_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1603_; 
v_ks_1582_ = lean_ctor_get(v_x_1531_, 0);
v_vs_1583_ = lean_ctor_get(v_x_1531_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1585_ = v_x_1531_;
v_isShared_1586_ = v_isSharedCheck_1603_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_vs_1583_);
lean_inc(v_ks_1582_);
lean_dec(v_x_1531_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1603_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_ks_1582_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_vs_1583_);
v___x_1588_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v_newNode_1589_; uint8_t v___y_1591_; size_t v___x_1597_; uint8_t v___x_1598_; 
v_newNode_1589_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v___x_1588_, v_x_1534_, v_x_1535_);
v___x_1597_ = ((size_t)7ULL);
v___x_1598_ = lean_usize_dec_le(v___x_1597_, v_x_1533_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1589_);
v___x_1600_ = lean_unsigned_to_nat(4u);
v___x_1601_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
lean_dec(v___x_1599_);
v___y_1591_ = v___x_1601_;
goto v___jp_1590_;
}
else
{
v___y_1591_ = v___x_1598_;
goto v___jp_1590_;
}
v___jp_1590_:
{
if (v___y_1591_ == 0)
{
lean_object* v_ks_1592_; lean_object* v_vs_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_ks_1592_ = lean_ctor_get(v_newNode_1589_, 0);
lean_inc_ref(v_ks_1592_);
v_vs_1593_ = lean_ctor_get(v_newNode_1589_, 1);
lean_inc_ref(v_vs_1593_);
lean_dec_ref(v_newNode_1589_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__2);
v___x_1596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1533_, v_ks_1592_, v_vs_1593_, v___x_1594_, v___x_1595_);
lean_dec_ref(v_vs_1593_);
lean_dec_ref(v_ks_1592_);
return v___x_1596_;
}
else
{
return v_newNode_1589_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_1604_, lean_object* v_keys_1605_, lean_object* v_vals_1606_, lean_object* v_i_1607_, lean_object* v_entries_1608_){
_start:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_array_get_size(v_keys_1605_);
v___x_1610_ = lean_nat_dec_lt(v_i_1607_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v_i_1607_);
return v_entries_1608_;
}
else
{
lean_object* v_k_1611_; lean_object* v_v_1612_; uint64_t v___x_1613_; size_t v_h_1614_; size_t v___x_1615_; lean_object* v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v_h_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_k_1611_ = lean_array_fget_borrowed(v_keys_1605_, v_i_1607_);
v_v_1612_ = lean_array_fget_borrowed(v_vals_1606_, v_i_1607_);
v___x_1613_ = l_Lean_instHashableMVarId_hash(v_k_1611_);
v_h_1614_ = lean_uint64_to_usize(v___x_1613_);
v___x_1615_ = ((size_t)5ULL);
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_sub(v_depth_1604_, v___x_1617_);
v___x_1619_ = lean_usize_mul(v___x_1615_, v___x_1618_);
v_h_1620_ = lean_usize_shift_right(v_h_1614_, v___x_1619_);
v___x_1621_ = lean_nat_add(v_i_1607_, v___x_1616_);
lean_dec(v_i_1607_);
lean_inc(v_v_1612_);
lean_inc(v_k_1611_);
v___x_1622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_entries_1608_, v_h_1620_, v_depth_1604_, v_k_1611_, v_v_1612_);
v_i_1607_ = v___x_1621_;
v_entries_1608_ = v___x_1622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_1624_, lean_object* v_keys_1625_, lean_object* v_vals_1626_, lean_object* v_i_1627_, lean_object* v_entries_1628_){
_start:
{
size_t v_depth_boxed_1629_; lean_object* v_res_1630_; 
v_depth_boxed_1629_ = lean_unbox_usize(v_depth_1624_);
lean_dec(v_depth_1624_);
v_res_1630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_1629_, v_keys_1625_, v_vals_1626_, v_i_1627_, v_entries_1628_);
lean_dec_ref(v_vals_1626_);
lean_dec_ref(v_keys_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
size_t v_x_1574__boxed_1636_; size_t v_x_1575__boxed_1637_; lean_object* v_res_1638_; 
v_x_1574__boxed_1636_ = lean_unbox_usize(v_x_1632_);
lean_dec(v_x_1632_);
v_x_1575__boxed_1637_ = lean_unbox_usize(v_x_1633_);
lean_dec(v_x_1633_);
v_res_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1631_, v_x_1574__boxed_1636_, v_x_1575__boxed_1637_, v_x_1634_, v_x_1635_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint64_t v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1642_ = l_Lean_instHashableMVarId_hash(v_x_1640_);
v___x_1643_ = lean_uint64_to_usize(v___x_1642_);
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1639_, v___x_1643_, v___x_1644_, v_x_1640_, v_x_1641_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(lean_object* v_mvarId_1646_, lean_object* v_val_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v_mctx_1651_; lean_object* v_cache_1652_; lean_object* v_zetaDeltaFVarIds_1653_; lean_object* v_postponed_1654_; lean_object* v_diag_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1683_; 
v___x_1650_ = lean_st_ref_take(v___y_1648_);
v_mctx_1651_ = lean_ctor_get(v___x_1650_, 0);
v_cache_1652_ = lean_ctor_get(v___x_1650_, 1);
v_zetaDeltaFVarIds_1653_ = lean_ctor_get(v___x_1650_, 2);
v_postponed_1654_ = lean_ctor_get(v___x_1650_, 3);
v_diag_1655_ = lean_ctor_get(v___x_1650_, 4);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1657_ = v___x_1650_;
v_isShared_1658_ = v_isSharedCheck_1683_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_diag_1655_);
lean_inc(v_postponed_1654_);
lean_inc(v_zetaDeltaFVarIds_1653_);
lean_inc(v_cache_1652_);
lean_inc(v_mctx_1651_);
lean_dec(v___x_1650_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1683_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v_depth_1659_; lean_object* v_levelAssignDepth_1660_; lean_object* v_lmvarCounter_1661_; lean_object* v_mvarCounter_1662_; lean_object* v_lDecls_1663_; lean_object* v_decls_1664_; lean_object* v_userNames_1665_; lean_object* v_lAssignment_1666_; lean_object* v_eAssignment_1667_; lean_object* v_dAssignment_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1682_; 
v_depth_1659_ = lean_ctor_get(v_mctx_1651_, 0);
v_levelAssignDepth_1660_ = lean_ctor_get(v_mctx_1651_, 1);
v_lmvarCounter_1661_ = lean_ctor_get(v_mctx_1651_, 2);
v_mvarCounter_1662_ = lean_ctor_get(v_mctx_1651_, 3);
v_lDecls_1663_ = lean_ctor_get(v_mctx_1651_, 4);
v_decls_1664_ = lean_ctor_get(v_mctx_1651_, 5);
v_userNames_1665_ = lean_ctor_get(v_mctx_1651_, 6);
v_lAssignment_1666_ = lean_ctor_get(v_mctx_1651_, 7);
v_eAssignment_1667_ = lean_ctor_get(v_mctx_1651_, 8);
v_dAssignment_1668_ = lean_ctor_get(v_mctx_1651_, 9);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_mctx_1651_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1670_ = v_mctx_1651_;
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_dAssignment_1668_);
lean_inc(v_eAssignment_1667_);
lean_inc(v_lAssignment_1666_);
lean_inc(v_userNames_1665_);
lean_inc(v_decls_1664_);
lean_inc(v_lDecls_1663_);
lean_inc(v_mvarCounter_1662_);
lean_inc(v_lmvarCounter_1661_);
lean_inc(v_levelAssignDepth_1660_);
lean_inc(v_depth_1659_);
lean_dec(v_mctx_1651_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_eAssignment_1667_, v_mvarId_1646_, v_val_1647_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 8, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_depth_1659_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_levelAssignDepth_1660_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_lmvarCounter_1661_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_mvarCounter_1662_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_lDecls_1663_);
lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_decls_1664_);
lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_userNames_1665_);
lean_ctor_set(v_reuseFailAlloc_1681_, 7, v_lAssignment_1666_);
lean_ctor_set(v_reuseFailAlloc_1681_, 8, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_dAssignment_1668_);
v___x_1674_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1674_);
v___x_1676_ = v___x_1657_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_cache_1652_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_zetaDeltaFVarIds_1653_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_postponed_1654_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_diag_1655_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_st_ref_set(v___y_1648_, v___x_1676_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg___boxed(lean_object* v_mvarId_1684_, lean_object* v_val_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1684_, v_val_1685_, v___y_1686_);
lean_dec(v___y_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(lean_object* v_a_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = l_Lean_Expr_mvarId_x21(v_x_1690_);
v___x_1692_ = l_Lean_instBEqMVarId_beq(v___x_1691_, v_a_1689_);
lean_dec(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed(lean_object* v_a_1693_, lean_object* v_x_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0(v_a_1693_, v_x_1694_);
lean_dec_ref(v_x_1694_);
lean_dec(v_a_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_argMVars_1697_, lean_object* v_argVars_1698_, lean_object* v_as_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_b_1702_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; lean_object* v_a_1711_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1710_ = lean_box(0);
v_a_1711_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
lean_inc(v_a_1711_);
v___f_1732_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1732_, 0, v_a_1711_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = l_Array_findIdx_x3f_loop___redArg(v___f_1732_, v_argMVars_1697_, v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_val_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1735_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Lean_instInhabitedExpr;
v___x_1737_ = lean_array_get_borrowed(v___x_1736_, v_argVars_1698_, v_val_1735_);
lean_dec(v_val_1735_);
lean_inc(v___x_1737_);
lean_inc(v_a_1711_);
v___x_1738_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_a_1711_, v___x_1737_, v___y_1704_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref(v___x_1738_);
v___y_1713_ = v___y_1703_;
v___y_1714_ = v___y_1704_;
v___y_1715_ = v___y_1705_;
v___y_1716_ = v___y_1706_;
goto v___jp_1712_;
}
else
{
return v___x_1738_;
}
}
else
{
lean_dec(v___x_1734_);
v___y_1713_ = v___y_1703_;
v___y_1714_ = v___y_1704_;
v___y_1715_ = v___y_1705_;
v___y_1716_ = v___y_1706_;
goto v___jp_1712_;
}
v___jp_1712_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_inc(v_a_1711_);
v___x_1717_ = l_Lean_Expr_mvar___override(v_a_1711_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
v___x_1718_ = lean_infer_type(v___x_1717_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1697_, v_argVars_1698_, v_a_1719_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1720_) == 0)
{
size_t v___x_1721_; size_t v___x_1722_; 
lean_dec_ref(v___x_1720_);
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_add(v_i_1701_, v___x_1721_);
v_i_1701_ = v___x_1722_;
v_b_1702_ = v___x_1710_;
goto _start;
}
else
{
return v___x_1720_;
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1718_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1718_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
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
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1739_, v_argVars_1740_, v_a_1748_, v_sz_1750_, v___x_1751_, v___x_1749_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_argMVars_1778_, lean_object* v_argVars_1779_, lean_object* v_as_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_argMVars_1778_, v_argVars_1779_, v_as_1780_, v_sz_boxed_1789_, v_i_boxed_1790_, v_b_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_mvarId_1792_, lean_object* v_val_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___redArg(v_mvarId_1792_, v_val_1793_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_mvarId_1800_, lean_object* v_val_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_mvarId_1800_, v_val_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0(lean_object* v_00_u03b2_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0___redArg(v_x_1809_, v_x_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, size_t v_x_1815_, size_t v_x_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___redArg(v_x_1814_, v_x_1815_, v_x_1816_, v_x_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
size_t v_x_1946__boxed_1826_; size_t v_x_1947__boxed_1827_; lean_object* v_res_1828_; 
v_x_1946__boxed_1826_ = lean_unbox_usize(v_x_1822_);
lean_dec(v_x_1822_);
v_x_1947__boxed_1827_ = lean_unbox_usize(v_x_1823_);
lean_dec(v_x_1823_);
v_res_1828_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1(v_00_u03b2_1820_, v_x_1821_, v_x_1946__boxed_1826_, v_x_1947__boxed_1827_, v_x_1824_, v_x_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1829_, lean_object* v_n_1830_, lean_object* v_k_1831_, lean_object* v_v_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1830_, v_k_1831_, v_v_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1834_, size_t v_depth_1835_, lean_object* v_keys_1836_, lean_object* v_vals_1837_, lean_object* v_heq_1838_, lean_object* v_i_1839_, lean_object* v_entries_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1835_, v_keys_1836_, v_vals_1837_, v_i_1839_, v_entries_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1842_, lean_object* v_depth_1843_, lean_object* v_keys_1844_, lean_object* v_vals_1845_, lean_object* v_heq_1846_, lean_object* v_i_1847_, lean_object* v_entries_1848_){
_start:
{
size_t v_depth_boxed_1849_; lean_object* v_res_1850_; 
v_depth_boxed_1849_ = lean_unbox_usize(v_depth_1843_);
lean_dec(v_depth_1843_);
v_res_1850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1842_, v_depth_boxed_1849_, v_keys_1844_, v_vals_1845_, v_heq_1846_, v_i_1847_, v_entries_1848_);
lean_dec_ref(v_vals_1845_);
lean_dec_ref(v_keys_1844_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_1852_, v_x_1853_, v_x_1854_, v_x_1855_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2039_, lean_object* v___x_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_b_2043_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_nat_dec_lt(v_a_2042_, v_upperBound_2039_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_a_2042_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_b_2043_);
return v___x_2046_;
}
else
{
lean_object* v_snd_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2088_; 
v_snd_2047_ = lean_ctor_get(v_b_2043_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_b_2043_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v_b_2043_, 0);
lean_dec(v_unused_2089_);
v___x_2049_ = v_b_2043_;
v_isShared_2050_ = v_isSharedCheck_2088_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_snd_2047_);
lean_dec(v_b_2043_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2088_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_array_2051_; lean_object* v_start_2052_; lean_object* v_stop_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_array_2051_ = lean_ctor_get(v_snd_2047_, 0);
v_start_2052_ = lean_ctor_get(v_snd_2047_, 1);
v_stop_2053_ = lean_ctor_get(v_snd_2047_, 2);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_nat_dec_lt(v_start_2052_, v_stop_2053_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2057_; 
lean_dec(v_a_2042_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2057_ = v___x_2049_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_snd_2047_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
else
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2084_; 
lean_inc(v_stop_2053_);
lean_inc(v_start_2052_);
lean_inc_ref(v_array_2051_);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_snd_2047_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; lean_object* v_unused_2086_; lean_object* v_unused_2087_; 
v_unused_2085_ = lean_ctor_get(v_snd_2047_, 2);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_snd_2047_, 1);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_snd_2047_, 0);
lean_dec(v_unused_2087_);
v___x_2061_ = v_snd_2047_;
v_isShared_2062_ = v_isSharedCheck_2084_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_snd_2047_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2084_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_nat_dec_eq(v___x_2040_, v___x_2063_);
v___x_2065_ = lean_array_fget(v_array_2051_, v_start_2052_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_add(v_start_2052_, v___x_2066_);
lean_dec(v_start_2052_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2067_);
v___x_2069_ = v___x_2061_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_array_2051_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_stop_2053_);
v___x_2069_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2041_, v_a_2042_);
if (v___x_2082_ == 0)
{
goto v___jp_2076_;
}
else
{
if (v___x_2064_ == 0)
{
lean_dec(v___x_2065_);
goto v___jp_2070_;
}
else
{
goto v___jp_2076_;
}
}
v___jp_2070_:
{
lean_object* v___x_2072_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2069_);
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2072_ = v___x_2049_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2069_);
v___x_2072_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_nat_add(v_a_2042_, v___x_2066_);
lean_dec(v_a_2042_);
v_a_2042_ = v___x_2073_;
v_b_2043_ = v___x_2072_;
goto _start;
}
}
v___jp_2076_:
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_Expr_hasExprMVar(v___x_2065_);
lean_dec(v___x_2065_);
if (v___x_2077_ == 0)
{
goto v___jp_2070_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_del_object(v___x_2049_);
lean_dec(v_a_2042_);
v___x_2078_ = lean_box(v___x_2064_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2069_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2090_, lean_object* v___x_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2090_, v___x_2091_, v_a_2092_, v_a_2093_, v_b_2094_);
lean_dec_ref(v_a_2092_);
lean_dec(v___x_2091_);
lean_dec(v_upperBound_2090_);
return v_res_2096_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2097_; lean_object* v_dummy_2098_; 
v___x_2097_ = lean_box(0);
v_dummy_2098_ = l_Lean_Expr_sort___override(v___x_2097_);
return v_dummy_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2099_, lean_object* v___x_2100_, uint8_t v___x_2101_, lean_object* v_x_2102_, lean_object* v_argTy_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
v___x_2109_ = lean_whnf(v_argTy_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2110_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v_dummy_2113_; lean_object* v_nargs_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
v_dummy_2113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2114_ = l_Lean_Expr_getAppNumArgs(v_a_2110_);
lean_inc(v_nargs_2114_);
v___x_2115_ = lean_mk_array(v_nargs_2114_, v_dummy_2113_);
v___x_2116_ = lean_unsigned_to_nat(1u);
v___x_2117_ = lean_nat_sub(v_nargs_2114_, v___x_2116_);
lean_dec(v_nargs_2114_);
v___x_2118_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2110_, v___x_2115_, v___x_2117_);
v___x_2119_ = lean_array_get_size(v___x_2118_);
lean_inc(v___x_2099_);
v___x_2120_ = l_Array_toSubarray___redArg(v___x_2118_, v___x_2099_, v___x_2119_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2120_);
v___x_2123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2119_, v___x_2100_, v_a_2112_, v___x_2099_, v___x_2122_);
lean_dec(v_a_2112_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2137_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; 
v_fst_2128_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_fst_2128_);
lean_dec(v_a_2124_);
if (lean_obj_tag(v_fst_2128_) == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(v___x_2101_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2129_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; 
v_val_2133_ = lean_ctor_get(v_fst_2128_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_fst_2128_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v_val_2133_);
v___x_2135_ = v___x_2126_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2123_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2123_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2110_);
lean_dec(v___x_2099_);
v_a_2146_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2111_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2111_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v___x_2099_);
v_a_2154_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2109_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2109_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v___x_2164_, lean_object* v_x_2165_, lean_object* v_argTy_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v___x_24484__boxed_2172_; lean_object* v_res_2173_; 
v___x_24484__boxed_2172_ = lean_unbox(v___x_2164_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2162_, v___x_2163_, v___x_24484__boxed_2172_, v_x_2165_, v_argTy_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_x_2165_);
lean_dec(v___x_2163_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2177_, lean_object* v_projInfo_x3f_2178_, lean_object* v___x_2179_, lean_object* v_argVars_2180_, lean_object* v_as_2181_, size_t v_sz_2182_, size_t v_i_2183_, lean_object* v_b_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_usize_dec_lt(v_i_2183_, v_sz_2182_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v___x_2179_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_b_2184_);
return v___x_2191_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec_ref(v_b_2184_);
v_a_2192_ = lean_array_uget_borrowed(v_as_2181_, v_i_2183_);
v___x_2193_ = l_Lean_instInhabitedExpr;
v___x_2194_ = lean_array_get_borrowed(v___x_2193_, v_fst_2177_, v_a_2192_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc(v___y_2186_);
lean_inc_ref(v___y_2185_);
lean_inc(v___x_2194_);
v___x_2195_ = lean_infer_type(v___x_2194_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2196_, v___y_2186_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2244_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2244_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2244_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2210_; lean_object* v___y_2212_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___f_2228_; uint8_t v___x_2229_; 
v___x_2202_ = lean_box(0);
v___x_2210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_box(v___x_2190_);
lean_inc(v___x_2179_);
v___f_2228_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2228_, 0, v___x_2226_);
lean_closure_set(v___f_2228_, 1, v___x_2179_);
lean_closure_set(v___f_2228_, 2, v___x_2227_);
v___x_2229_ = lean_nat_dec_eq(v___x_2179_, v___x_2226_);
if (lean_obj_tag(v_projInfo_x3f_2178_) == 1)
{
lean_object* v_val_2230_; lean_object* v_numParams_2231_; uint8_t v___x_2232_; 
v_val_2230_ = lean_ctor_get(v_projInfo_x3f_2178_, 0);
v_numParams_2231_ = lean_ctor_get(v_val_2230_, 1);
v___x_2232_ = lean_nat_dec_eq(v_numParams_2231_, v_a_2192_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2198_, v___f_2228_, v___x_2229_, v___x_2229_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
v___y_2212_ = v___x_2233_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2234_; 
lean_dec_ref(v___f_2228_);
lean_dec(v___x_2179_);
v___x_2234_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2177_, v_argVars_2180_, v_a_2198_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_dec_ref(v___x_2234_);
goto v___jp_2203_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_del_object(v___x_2200_);
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
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
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2198_, v___f_2228_, v___x_2229_, v___x_2229_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
v___y_2212_ = v___x_2243_;
goto v___jp_2211_;
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_inc(v_a_2192_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_a_2192_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2202_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2206_);
v___x_2208_ = v___x_2200_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
v___jp_2211_:
{
if (lean_obj_tag(v___y_2212_) == 0)
{
lean_object* v_a_2213_; uint8_t v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___y_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___y_2212_);
v___x_2214_ = lean_unbox(v_a_2213_);
lean_dec(v_a_2213_);
if (v___x_2214_ == 0)
{
size_t v___x_2215_; size_t v___x_2216_; 
lean_del_object(v___x_2200_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_add(v_i_2183_, v___x_2215_);
v_i_2183_ = v___x_2216_;
v_b_2184_ = v___x_2210_;
goto _start;
}
else
{
lean_dec(v___x_2179_);
goto v___jp_2203_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2200_);
lean_dec(v___x_2179_);
v_a_2218_ = lean_ctor_get(v___y_2212_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___y_2212_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___y_2212_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___y_2212_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v___x_2179_);
v_a_2245_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2197_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2197_);
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
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v___x_2179_);
v_a_2253_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2195_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2195_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2261_, lean_object* v_projInfo_x3f_2262_, lean_object* v___x_2263_, lean_object* v_argVars_2264_, lean_object* v_as_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2261_, v_projInfo_x3f_2262_, v___x_2263_, v_argVars_2264_, v_as_2265_, v_sz_boxed_2274_, v_i_boxed_2275_, v_b_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_as_2265_);
lean_dec_ref(v_argVars_2264_);
lean_dec(v_projInfo_x3f_2262_);
lean_dec_ref(v_fst_2261_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v_env_2284_; lean_object* v___x_2285_; lean_object* v_mctx_2286_; lean_object* v_lctx_2287_; lean_object* v_options_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2283_ = lean_st_ref_get(v___y_2281_);
v_env_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref(v_env_2284_);
lean_dec(v___x_2283_);
v___x_2285_ = lean_st_ref_get(v___y_2279_);
v_mctx_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_mctx_2286_);
lean_dec(v___x_2285_);
v_lctx_2287_ = lean_ctor_get(v___y_2278_, 2);
v_options_2288_ = lean_ctor_get(v___y_2280_, 2);
lean_inc_ref(v_options_2288_);
lean_inc_ref(v_lctx_2287_);
v___x_2289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2289_, 0, v_env_2284_);
lean_ctor_set(v___x_2289_, 1, v_mctx_2286_);
lean_ctor_set(v___x_2289_, 2, v_lctx_2287_);
lean_ctor_set(v___x_2289_, 3, v_options_2288_);
v___x_2290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v_msgData_2277_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_ref_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_ref_2305_ = lean_ctor_get(v___y_2302_, 5);
v___x_2306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_inc(v_ref_2305_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_ref_2305_);
lean_ctor_set(v___x_2311_, 1, v_a_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 1);
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2323_, lean_object* v_as_2324_, size_t v_i_2325_, size_t v_stop_2326_, lean_object* v_b_2327_){
_start:
{
lean_object* v___y_2329_; uint8_t v___x_2333_; 
v___x_2333_ = lean_usize_dec_eq(v_i_2325_, v_stop_2326_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_array_uget_borrowed(v_as_2324_, v_i_2325_);
v___x_2335_ = lean_nat_dec_eq(v___x_2334_, v_next_2323_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_inc(v___x_2334_);
v___x_2336_ = lean_array_push(v_b_2327_, v___x_2334_);
v___y_2329_ = v___x_2336_;
goto v___jp_2328_;
}
else
{
v___y_2329_ = v_b_2327_;
goto v___jp_2328_;
}
}
else
{
return v_b_2327_;
}
v___jp_2328_:
{
size_t v___x_2330_; size_t v___x_2331_; 
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_add(v_i_2325_, v___x_2330_);
v_i_2325_ = v___x_2331_;
v_b_2327_ = v___y_2329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2337_, lean_object* v_as_2338_, lean_object* v_i_2339_, lean_object* v_stop_2340_, lean_object* v_b_2341_){
_start:
{
size_t v_i_boxed_2342_; size_t v_stop_boxed_2343_; lean_object* v_res_2344_; 
v_i_boxed_2342_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_stop_boxed_2343_ = lean_unbox_usize(v_stop_2340_);
lean_dec(v_stop_2340_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2337_, v_as_2338_, v_i_boxed_2342_, v_stop_boxed_2343_, v_b_2341_);
lean_dec_ref(v_as_2338_);
lean_dec(v_next_2337_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_bs_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2347_, v_sz_2346_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_bs_2348_);
return v___x_2355_;
}
else
{
lean_object* v_v_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_v_2356_ = lean_array_uget_borrowed(v_bs_2348_, v_i_2347_);
v___x_2357_ = l_Lean_instInhabitedExpr;
v___x_2358_ = lean_array_get_borrowed(v___x_2357_, v_fst_2345_, v_v_2356_);
lean_inc(v___y_2352_);
lean_inc_ref(v___y_2351_);
lean_inc(v___y_2350_);
lean_inc_ref(v___y_2349_);
lean_inc(v___x_2358_);
v___x_2359_ = lean_infer_type(v___x_2358_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2360_, v___y_2350_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v_bs_x27_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v_bs_x27_2364_ = lean_array_uset(v_bs_2348_, v_i_2347_, v___x_2363_);
v___x_2365_ = l_Lean_Expr_setPPExplicit(v_a_2362_, v___x_2354_);
v___x_2366_ = l_Lean_indentExpr(v___x_2365_);
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2347_, v___x_2367_);
v___x_2369_ = lean_array_uset(v_bs_x27_2364_, v_i_2347_, v___x_2366_);
v_i_2347_ = v___x_2368_;
v_bs_2348_ = v___x_2369_;
goto _start;
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v_bs_2348_);
v_a_2371_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2361_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2361_);
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
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v_bs_2348_);
v_a_2379_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2359_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2359_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2387_, lean_object* v_sz_2388_, lean_object* v_i_2389_, lean_object* v_bs_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2388_);
lean_dec(v_sz_2388_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2389_);
lean_dec(v_i_2389_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2387_, v_sz_boxed_2396_, v_i_boxed_2397_, v_bs_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_fst_2387_);
return v_res_2398_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__1));
v___x_2403_ = l_Lean_MessageData_ofFormat(v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__3));
v___x_2406_ = l_Lean_stringToMessageData(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__5));
v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__7));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_2413_, lean_object* v_argVars_2414_, lean_object* v_inst_2415_, lean_object* v_a_2416_, lean_object* v_projInfo_x3f_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2555_; 
v_fst_2464_ = lean_ctor_get(v_b_2418_, 0);
v_snd_2465_ = lean_ctor_get(v_b_2418_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_b_2418_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2467_ = v_b_2418_;
v_isShared_2468_ = v_isSharedCheck_2555_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v_b_2418_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2555_;
goto v_resetjp_2466_;
}
v___jp_2424_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = l_Lean_instInhabitedExpr;
v___x_2433_ = lean_array_get_borrowed(v___x_2432_, v_fst_2413_, v___y_2428_);
lean_dec(v___y_2428_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2426_);
lean_inc(v___x_2433_);
v___x_2434_ = lean_infer_type(v___x_2433_, v___y_2426_, v___y_2430_, v___y_2429_, v___y_2425_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2413_, v_argVars_2414_, v_a_2435_, v___y_2426_, v___y_2430_, v___y_2429_, v___y_2425_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref(v___x_2436_);
lean_inc(v___x_2433_);
v___x_2437_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2413_, v_argVars_2414_, v___x_2433_, v___y_2426_, v___y_2430_, v___y_2429_, v___y_2425_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2438_; 
lean_dec_ref(v___x_2437_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2427_);
lean_ctor_set(v___x_2438_, 1, v___y_2431_);
v_b_2418_ = v___x_2438_;
goto _start;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v___y_2431_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2440_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2437_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2437_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref(v___y_2431_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2448_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v___y_2431_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2456_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2434_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2434_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
v_resetjp_2466_:
{
lean_object* v_next_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = lean_array_get_size(v_snd_2465_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_nat_dec_eq(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; size_t v_sz_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
lean_del_object(v___x_2467_);
v___x_2535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2536_ = lean_array_size(v_snd_2465_);
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2413_, v_projInfo_x3f_2417_, v___x_2532_, v_argVars_2414_, v_snd_2465_, v_sz_2536_, v___x_2537_, v___x_2535_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_fst_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v_fst_2540_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_fst_2540_);
lean_dec(v_a_2539_);
if (lean_obj_tag(v_fst_2540_) == 0)
{
goto v___jp_2494_;
}
else
{
lean_object* v_val_2541_; 
v_val_2541_ = lean_ctor_get(v_fst_2540_, 0);
lean_inc(v_val_2541_);
lean_dec_ref(v_fst_2540_);
if (lean_obj_tag(v_val_2541_) == 0)
{
goto v___jp_2494_;
}
else
{
lean_object* v_val_2542_; 
v_val_2542_ = lean_ctor_get(v_val_2541_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v_val_2541_);
v_next_2470_ = v_val_2542_;
v___y_2471_ = v___y_2419_;
v___y_2472_ = v___y_2420_;
v___y_2473_ = v___y_2421_;
v___y_2474_ = v___y_2422_;
goto v___jp_2469_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_snd_2465_);
lean_dec(v_fst_2464_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2543_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2538_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2538_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v___x_2552_; 
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
if (v_isShared_2468_ == 0)
{
v___x_2552_ = v___x_2467_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_fst_2464_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_snd_2465_);
v___x_2552_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
v___jp_2469_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
lean_inc(v_next_2470_);
v___x_2475_ = lean_array_push(v_fst_2464_, v_next_2470_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_array_get_size(v_snd_2465_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2479_ = lean_nat_dec_lt(v___x_2476_, v___x_2477_);
if (v___x_2479_ == 0)
{
lean_dec(v_snd_2465_);
v___y_2425_ = v___y_2474_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___x_2475_;
v___y_2428_ = v_next_2470_;
v___y_2429_ = v___y_2473_;
v___y_2430_ = v___y_2472_;
v___y_2431_ = v___x_2478_;
goto v___jp_2424_;
}
else
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_nat_dec_le(v___x_2477_, v___x_2477_);
if (v___x_2480_ == 0)
{
if (v___x_2479_ == 0)
{
lean_dec(v_snd_2465_);
v___y_2425_ = v___y_2474_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___x_2475_;
v___y_2428_ = v_next_2470_;
v___y_2429_ = v___y_2473_;
v___y_2430_ = v___y_2472_;
v___y_2431_ = v___x_2478_;
goto v___jp_2424_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2477_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2470_, v_snd_2465_, v___x_2481_, v___x_2482_, v___x_2478_);
lean_dec(v_snd_2465_);
v___y_2425_ = v___y_2474_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___x_2475_;
v___y_2428_ = v_next_2470_;
v___y_2429_ = v___y_2473_;
v___y_2430_ = v___y_2472_;
v___y_2431_ = v___x_2483_;
goto v___jp_2424_;
}
}
else
{
size_t v___x_2484_; size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = lean_usize_of_nat(v___x_2477_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2470_, v_snd_2465_, v___x_2484_, v___x_2485_, v___x_2478_);
lean_dec(v_snd_2465_);
v___y_2425_ = v___y_2474_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___x_2475_;
v___y_2428_ = v_next_2470_;
v___y_2429_ = v___y_2473_;
v___y_2430_ = v___y_2472_;
v___y_2431_ = v___x_2486_;
goto v___jp_2424_;
}
}
}
v___jp_2487_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = lean_array_get_borrowed(v___x_2492_, v_snd_2465_, v___x_2492_);
lean_inc(v___x_2493_);
v_next_2470_ = v___x_2493_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
goto v___jp_2469_;
}
v___jp_2494_:
{
lean_object* v_options_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_options_2495_ = lean_ctor_get(v___y_2421_, 2);
v___x_2496_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2497_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
v___y_2488_ = v___y_2419_;
v___y_2489_ = v___y_2420_;
v___y_2490_ = v___y_2421_;
v___y_2491_ = v___y_2422_;
goto v___jp_2487_;
}
else
{
size_t v_sz_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v_sz_2498_ = lean_array_size(v_snd_2465_);
v___x_2499_ = ((size_t)0ULL);
lean_inc(v_snd_2465_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2413_, v_sz_2498_, v___x_2499_, v_snd_2465_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = lean_array_to_list(v_a_2501_);
v___x_2503_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2504_ = l_Lean_MessageData_joinSep(v___x_2502_, v___x_2503_);
v___x_2505_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__4);
lean_inc_ref(v_inst_2415_);
v___x_2506_ = l_Lean_MessageData_ofExpr(v_inst_2415_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__6);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_inc_ref(v_a_2416_);
v___x_2510_ = l_Lean_indentExpr(v_a_2416_);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__8);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2504_);
v___x_2515_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2514_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref(v___x_2515_);
v___y_2488_ = v___y_2419_;
v___y_2489_ = v___y_2420_;
v___y_2490_ = v___y_2421_;
v___y_2491_ = v___y_2422_;
goto v___jp_2487_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_snd_2465_);
lean_dec(v_fst_2464_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_snd_2465_);
lean_dec(v_fst_2464_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_inst_2415_);
v_a_2524_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2500_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2500_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_2556_, lean_object* v_argVars_2557_, lean_object* v_inst_2558_, lean_object* v_a_2559_, lean_object* v_projInfo_x3f_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2556_, v_argVars_2557_, v_inst_2558_, v_a_2559_, v_projInfo_x3f_2560_, v_b_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v_projInfo_x3f_2560_);
lean_dec_ref(v_argVars_2557_);
lean_dec_ref(v_fst_2556_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2568_, size_t v_sz_2569_, size_t v_i_2570_, lean_object* v_bs_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_usize_dec_lt(v_i_2570_, v_sz_2569_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_bs_2571_);
return v___x_2578_;
}
else
{
lean_object* v_v_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_v_2579_ = lean_array_uget_borrowed(v_bs_2571_, v_i_2570_);
v___x_2580_ = l_Lean_instInhabitedExpr;
v___x_2581_ = lean_array_get_borrowed(v___x_2580_, v_argVars_2568_, v_v_2579_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc_ref(v___y_2572_);
lean_inc(v___x_2581_);
v___x_2582_ = lean_infer_type(v___x_2581_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v_bs_x27_2585_; lean_object* v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v_bs_x27_2585_ = lean_array_uset(v_bs_2571_, v_i_2570_, v___x_2584_);
v___x_2586_ = l_Lean_indentExpr(v_a_2583_);
v___x_2587_ = ((size_t)1ULL);
v___x_2588_ = lean_usize_add(v_i_2570_, v___x_2587_);
v___x_2589_ = lean_array_uset(v_bs_x27_2585_, v_i_2570_, v___x_2586_);
v_i_2570_ = v___x_2588_;
v_bs_2571_ = v___x_2589_;
goto _start;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_bs_2571_);
v_a_2591_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2582_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2582_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2599_, lean_object* v_sz_2600_, lean_object* v_i_2601_, lean_object* v_bs_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
size_t v_sz_boxed_2608_; size_t v_i_boxed_2609_; lean_object* v_res_2610_; 
v_sz_boxed_2608_ = lean_unbox_usize(v_sz_2600_);
lean_dec(v_sz_2600_);
v_i_boxed_2609_ = lean_unbox_usize(v_i_2601_);
lean_dec(v_i_2601_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2599_, v_sz_boxed_2608_, v_i_boxed_2609_, v_bs_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_argVars_2599_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = l_List_reverse___redArg(v_a_2612_);
return v___x_2613_;
}
else
{
lean_object* v_head_2614_; lean_object* v_tail_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2626_; 
v_head_2614_ = lean_ctor_get(v_a_2611_, 0);
v_tail_2615_ = lean_ctor_get(v_a_2611_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_a_2611_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2617_ = v_a_2611_;
v_isShared_2618_ = v_isSharedCheck_2626_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_tail_2615_);
lean_inc(v_head_2614_);
lean_dec(v_a_2611_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2626_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2619_ = l_Nat_reprFast(v_head_2614_);
v___x_2620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
v___x_2621_ = l_Lean_MessageData_ofFormat(v___x_2620_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v_a_2612_);
lean_ctor_set(v___x_2617_, 0, v___x_2621_);
v___x_2623_ = v___x_2617_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_a_2612_);
v___x_2623_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
v_a_2611_ = v_tail_2615_;
v_a_2612_ = v___x_2623_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2627_; double v___x_2628_; 
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_float_of_nat(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2631_, lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_ref_2638_; lean_object* v___x_2639_; lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2684_; 
v_ref_2638_ = lean_ctor_get(v___y_2635_, 5);
v___x_2639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v_traceState_2645_; lean_object* v_env_2646_; lean_object* v_nextMacroScope_2647_; lean_object* v_ngen_2648_; lean_object* v_auxDeclNGen_2649_; lean_object* v_cache_2650_; lean_object* v_messages_2651_; lean_object* v_infoState_2652_; lean_object* v_snapshotTasks_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2683_; 
v___x_2644_ = lean_st_ref_take(v___y_2636_);
v_traceState_2645_ = lean_ctor_get(v___x_2644_, 4);
v_env_2646_ = lean_ctor_get(v___x_2644_, 0);
v_nextMacroScope_2647_ = lean_ctor_get(v___x_2644_, 1);
v_ngen_2648_ = lean_ctor_get(v___x_2644_, 2);
v_auxDeclNGen_2649_ = lean_ctor_get(v___x_2644_, 3);
v_cache_2650_ = lean_ctor_get(v___x_2644_, 5);
v_messages_2651_ = lean_ctor_get(v___x_2644_, 6);
v_infoState_2652_ = lean_ctor_get(v___x_2644_, 7);
v_snapshotTasks_2653_ = lean_ctor_get(v___x_2644_, 8);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snapshotTasks_2653_);
lean_inc(v_infoState_2652_);
lean_inc(v_messages_2651_);
lean_inc(v_cache_2650_);
lean_inc(v_traceState_2645_);
lean_inc(v_auxDeclNGen_2649_);
lean_inc(v_ngen_2648_);
lean_inc(v_nextMacroScope_2647_);
lean_inc(v_env_2646_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint64_t v_tid_2657_; lean_object* v_traces_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2682_; 
v_tid_2657_ = lean_ctor_get_uint64(v_traceState_2645_, sizeof(void*)*1);
v_traces_2658_ = lean_ctor_get(v_traceState_2645_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_traceState_2645_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2660_ = v_traceState_2645_;
v_isShared_2661_ = v_isSharedCheck_2682_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_traces_2658_);
lean_dec(v_traceState_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2682_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; double v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2662_ = lean_box(0);
v___x_2663_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2664_ = 0;
v___x_2665_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
v___x_2666_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2666_, 0, v_cls_2631_);
lean_ctor_set(v___x_2666_, 1, v___x_2662_);
lean_ctor_set(v___x_2666_, 2, v___x_2665_);
lean_ctor_set_float(v___x_2666_, sizeof(void*)*3, v___x_2663_);
lean_ctor_set_float(v___x_2666_, sizeof(void*)*3 + 8, v___x_2663_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*3 + 16, v___x_2664_);
v___x_2667_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2668_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v_a_2640_);
lean_ctor_set(v___x_2668_, 2, v___x_2667_);
lean_inc(v_ref_2638_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_ref_2638_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_PersistentArray_push___redArg(v_traces_2658_, v___x_2669_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2670_);
v___x_2672_ = v___x_2660_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2670_);
lean_ctor_set_uint64(v_reuseFailAlloc_2681_, sizeof(void*)*1, v_tid_2657_);
v___x_2672_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v___x_2672_);
v___x_2674_ = v___x_2655_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_env_2646_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_nextMacroScope_2647_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_ngen_2648_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_auxDeclNGen_2649_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2680_, 5, v_cache_2650_);
lean_ctor_set(v_reuseFailAlloc_2680_, 6, v_messages_2651_);
lean_ctor_set(v_reuseFailAlloc_2680_, 7, v_infoState_2652_);
lean_ctor_set(v_reuseFailAlloc_2680_, 8, v_snapshotTasks_2653_);
v___x_2674_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2675_ = lean_st_ref_set(v___y_2636_, v___x_2674_);
v___x_2676_ = lean_box(0);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2676_);
v___x_2678_ = v___x_2642_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2685_, lean_object* v_msg_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2685_, v_msg_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2702_ = l_Lean_Name_append(v___x_2701_, v___x_2700_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2705_ = l_Lean_stringToMessageData(v___x_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2715_, lean_object* v_fst_2716_, lean_object* v_fst_2717_, lean_object* v_inst_2718_, lean_object* v_a_2719_, lean_object* v_projInfo_x3f_2720_, lean_object* v_argVars_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2715_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v_dummy_2730_; lean_object* v_nargs_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; size_t v_sz_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref(v___x_2728_);
v_dummy_2730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2731_ = l_Lean_Expr_getAppNumArgs(v_a_2715_);
lean_inc(v_nargs_2731_);
v___x_2732_ = lean_mk_array(v_nargs_2731_, v_dummy_2730_);
v___x_2733_ = lean_unsigned_to_nat(1u);
v___x_2734_ = lean_nat_sub(v_nargs_2731_, v___x_2733_);
lean_dec(v_nargs_2731_);
lean_inc_ref(v_a_2715_);
v___x_2735_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2715_, v___x_2732_, v___x_2734_);
v___x_2736_ = lean_array_get_size(v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___x_2736_);
v_sz_2739_ = lean_array_size(v___x_2735_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2729_, v_fst_2716_, v_argVars_2721_, v___x_2735_, v_sz_2739_, v___x_2740_, v___x_2738_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec_ref(v___x_2735_);
lean_dec(v_a_2729_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec_ref(v___x_2741_);
v___x_2742_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2743_ = lean_array_get_size(v_fst_2716_);
v___x_2744_ = l_List_range(v___x_2743_);
v___x_2745_ = lean_box(0);
v___x_2746_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2717_, v___x_2744_, v___x_2745_);
v___x_2747_ = lean_array_mk(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2742_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc_ref(v_inst_2718_);
v___x_2749_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_2716_, v_argVars_2721_, v_inst_2718_, v_a_2719_, v_projInfo_x3f_2720_, v___x_2748_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2842_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2842_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2842_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_fst_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2840_; 
v_fst_2754_ = lean_ctor_get(v_a_2750_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v_a_2750_, 1);
lean_dec(v_unused_2841_);
v___x_2756_ = v_a_2750_;
v_isShared_2757_ = v_isSharedCheck_2840_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_fst_2754_);
lean_dec(v_a_2750_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2840_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_options_2762_; lean_object* v_inheritedTraceOptions_2763_; lean_object* v___y_2764_; lean_object* v_options_2820_; lean_object* v_inheritedTraceOptions_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_options_2820_ = lean_ctor_get(v___y_2725_, 2);
v_inheritedTraceOptions_2821_ = lean_ctor_get(v___y_2725_, 13);
v___x_2822_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2823_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2820_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec_ref(v_a_2715_);
v___y_2759_ = v___y_2723_;
v___y_2760_ = v___y_2724_;
v___y_2761_ = v___y_2725_;
v_options_2762_ = v_options_2820_;
v_inheritedTraceOptions_2763_ = v_inheritedTraceOptions_2821_;
v___y_2764_ = v___y_2726_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2824_; lean_object* v_a_2825_; uint8_t v___x_2826_; 
v___x_2824_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2715_, v___y_2724_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_Expr_hasExprMVar(v_a_2825_);
if (v___x_2826_ == 0)
{
lean_dec(v_a_2825_);
v___y_2759_ = v___y_2723_;
v___y_2760_ = v___y_2724_;
v___y_2761_ = v___y_2725_;
v_options_2762_ = v_options_2820_;
v_inheritedTraceOptions_2763_ = v_inheritedTraceOptions_2821_;
v___y_2764_ = v___y_2726_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_del_object(v___x_2756_);
lean_dec(v_fst_2754_);
lean_del_object(v___x_2752_);
lean_dec_ref(v_inst_2718_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2828_ = l_Lean_Expr_setPPExplicit(v_a_2825_, v___x_2826_);
v___x_2829_ = l_Lean_indentExpr(v___x_2828_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2827_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2830_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
v___jp_2758_:
{
uint8_t v_hasTrace_2765_; 
v_hasTrace_2765_ = lean_ctor_get_uint8(v_options_2762_, sizeof(void*)*1);
if (v_hasTrace_2765_ == 0)
{
lean_object* v___x_2767_; 
lean_del_object(v___x_2756_);
lean_dec_ref(v_inst_2718_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_fst_2754_);
v___x_2767_ = v___x_2752_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2754_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2770_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2763_, v_options_2762_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; 
lean_del_object(v___x_2756_);
lean_dec_ref(v_inst_2718_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_fst_2754_);
v___x_2773_ = v___x_2752_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_fst_2754_);
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
size_t v_sz_2775_; lean_object* v___x_2776_; 
lean_del_object(v___x_2752_);
v_sz_2775_ = lean_array_size(v_fst_2754_);
lean_inc(v_fst_2754_);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2721_, v_sz_2775_, v___x_2740_, v_fst_2754_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2764_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2779_ = l_Lean_MessageData_ofExpr(v_inst_2718_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 7);
lean_ctor_set(v___x_2756_, 1, v___x_2779_);
lean_ctor_set(v___x_2756_, 0, v___x_2778_);
v___x_2781_ = v___x_2756_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2782_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
lean_inc(v_fst_2754_);
v___x_2784_ = lean_array_to_list(v_fst_2754_);
v___x_2785_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2784_, v___x_2745_);
v___x_2786_ = l_Lean_MessageData_ofList(v___x_2785_);
v___x_2787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2783_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_array_to_list(v_a_2777_);
v___x_2791_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__2);
v___x_2792_ = l_Lean_MessageData_joinSep(v___x_2790_, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2789_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2769_, v___x_2793_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2764_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2794_, 0);
lean_dec(v_unused_2802_);
v___x_2796_ = v___x_2794_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v___x_2794_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_fst_2754_);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_fst_2754_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_fst_2754_);
v_a_2803_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2794_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2794_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_del_object(v___x_2756_);
lean_dec(v_fst_2754_);
lean_dec_ref(v_inst_2718_);
v_a_2812_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2776_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2776_);
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
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_inst_2718_);
lean_dec_ref(v_a_2715_);
v_a_2843_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2749_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2749_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v_a_2719_);
lean_dec_ref(v_inst_2718_);
lean_dec_ref(v_a_2715_);
v_a_2851_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2741_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2741_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_dec_ref(v_a_2719_);
lean_dec_ref(v_inst_2718_);
lean_dec_ref(v_a_2715_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2859_, lean_object* v_fst_2860_, lean_object* v_fst_2861_, lean_object* v_inst_2862_, lean_object* v_a_2863_, lean_object* v_projInfo_x3f_2864_, lean_object* v_argVars_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2859_, v_fst_2860_, v_fst_2861_, v_inst_2862_, v_a_2863_, v_projInfo_x3f_2864_, v_argVars_2865_, v_x_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec_ref(v_x_2866_);
lean_dec_ref(v_argVars_2865_);
lean_dec(v_projInfo_x3f_2864_);
lean_dec_ref(v_fst_2861_);
lean_dec_ref(v_fst_2860_);
return v_res_2872_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_2873_; uint64_t v___x_2874_; 
v___x_2873_ = 2;
v___x_2874_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2875_, lean_object* v_projInfo_x3f_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; uint8_t v_foApprox_2883_; uint8_t v_ctxApprox_2884_; uint8_t v_quasiPatternApprox_2885_; uint8_t v_constApprox_2886_; uint8_t v_isDefEqStuckEx_2887_; uint8_t v_unificationHints_2888_; uint8_t v_proofIrrelevance_2889_; uint8_t v_assignSyntheticOpaque_2890_; uint8_t v_offsetCnstrs_2891_; uint8_t v_etaStruct_2892_; uint8_t v_univApprox_2893_; uint8_t v_iota_2894_; uint8_t v_beta_2895_; uint8_t v_proj_2896_; uint8_t v_zeta_2897_; uint8_t v_zetaDelta_2898_; uint8_t v_zetaUnused_2899_; uint8_t v_zetaHave_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2965_; 
v___x_2882_ = l_Lean_Meta_Context_config(v_a_2877_);
v_foApprox_2883_ = lean_ctor_get_uint8(v___x_2882_, 0);
v_ctxApprox_2884_ = lean_ctor_get_uint8(v___x_2882_, 1);
v_quasiPatternApprox_2885_ = lean_ctor_get_uint8(v___x_2882_, 2);
v_constApprox_2886_ = lean_ctor_get_uint8(v___x_2882_, 3);
v_isDefEqStuckEx_2887_ = lean_ctor_get_uint8(v___x_2882_, 4);
v_unificationHints_2888_ = lean_ctor_get_uint8(v___x_2882_, 5);
v_proofIrrelevance_2889_ = lean_ctor_get_uint8(v___x_2882_, 6);
v_assignSyntheticOpaque_2890_ = lean_ctor_get_uint8(v___x_2882_, 7);
v_offsetCnstrs_2891_ = lean_ctor_get_uint8(v___x_2882_, 8);
v_etaStruct_2892_ = lean_ctor_get_uint8(v___x_2882_, 10);
v_univApprox_2893_ = lean_ctor_get_uint8(v___x_2882_, 11);
v_iota_2894_ = lean_ctor_get_uint8(v___x_2882_, 12);
v_beta_2895_ = lean_ctor_get_uint8(v___x_2882_, 13);
v_proj_2896_ = lean_ctor_get_uint8(v___x_2882_, 14);
v_zeta_2897_ = lean_ctor_get_uint8(v___x_2882_, 15);
v_zetaDelta_2898_ = lean_ctor_get_uint8(v___x_2882_, 16);
v_zetaUnused_2899_ = lean_ctor_get_uint8(v___x_2882_, 17);
v_zetaHave_2900_ = lean_ctor_get_uint8(v___x_2882_, 18);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2902_ = v___x_2882_;
v_isShared_2903_ = v_isSharedCheck_2965_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v___x_2882_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2965_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
uint8_t v_trackZetaDelta_2904_; lean_object* v_zetaDeltaSet_2905_; lean_object* v_lctx_2906_; lean_object* v_localInstances_2907_; lean_object* v_defEqCtx_x3f_2908_; lean_object* v_synthPendingDepth_2909_; lean_object* v_canUnfold_x3f_2910_; uint8_t v_univApprox_2911_; uint8_t v_inTypeClassResolution_2912_; uint8_t v_cacheInferType_2913_; uint8_t v___x_2914_; lean_object* v_config_2916_; 
v_trackZetaDelta_2904_ = lean_ctor_get_uint8(v_a_2877_, sizeof(void*)*7);
v_zetaDeltaSet_2905_ = lean_ctor_get(v_a_2877_, 1);
v_lctx_2906_ = lean_ctor_get(v_a_2877_, 2);
v_localInstances_2907_ = lean_ctor_get(v_a_2877_, 3);
v_defEqCtx_x3f_2908_ = lean_ctor_get(v_a_2877_, 4);
v_synthPendingDepth_2909_ = lean_ctor_get(v_a_2877_, 5);
v_canUnfold_x3f_2910_ = lean_ctor_get(v_a_2877_, 6);
v_univApprox_2911_ = lean_ctor_get_uint8(v_a_2877_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2912_ = lean_ctor_get_uint8(v_a_2877_, sizeof(void*)*7 + 2);
v_cacheInferType_2913_ = lean_ctor_get_uint8(v_a_2877_, sizeof(void*)*7 + 3);
v___x_2914_ = 2;
if (v_isShared_2903_ == 0)
{
v_config_2916_ = v___x_2902_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 0, v_foApprox_2883_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 1, v_ctxApprox_2884_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 2, v_quasiPatternApprox_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 3, v_constApprox_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 4, v_isDefEqStuckEx_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 5, v_unificationHints_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 6, v_proofIrrelevance_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 7, v_assignSyntheticOpaque_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 8, v_offsetCnstrs_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 10, v_etaStruct_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 11, v_univApprox_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 12, v_iota_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 13, v_beta_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 14, v_proj_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 15, v_zeta_2897_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 16, v_zetaDelta_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 17, v_zetaUnused_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, 18, v_zetaHave_2900_);
v_config_2916_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v_key_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_ctor_set_uint8(v_config_2916_, 9, v___x_2914_);
v___x_2917_ = l_Lean_Meta_Context_configKey(v_a_2877_);
v___x_2918_ = 2ULL;
v___x_2919_ = lean_uint64_shift_right(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_uint64_shift_left(v___x_2919_, v___x_2918_);
v___x_2921_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_2922_ = lean_uint64_lor(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2923_, 0, v_config_2916_);
lean_ctor_set_uint64(v___x_2923_, sizeof(void*)*1, v_key_2922_);
lean_inc(v_canUnfold_x3f_2910_);
lean_inc(v_synthPendingDepth_2909_);
lean_inc(v_defEqCtx_x3f_2908_);
lean_inc_ref(v_localInstances_2907_);
lean_inc_ref(v_lctx_2906_);
lean_inc(v_zetaDeltaSet_2905_);
v___x_2924_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v_zetaDeltaSet_2905_);
lean_ctor_set(v___x_2924_, 2, v_lctx_2906_);
lean_ctor_set(v___x_2924_, 3, v_localInstances_2907_);
lean_ctor_set(v___x_2924_, 4, v_defEqCtx_x3f_2908_);
lean_ctor_set(v___x_2924_, 5, v_synthPendingDepth_2909_);
lean_ctor_set(v___x_2924_, 6, v_canUnfold_x3f_2910_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7, v_trackZetaDelta_2904_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 1, v_univApprox_2911_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2912_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 3, v_cacheInferType_2913_);
lean_inc(v_a_2880_);
lean_inc_ref(v_a_2879_);
lean_inc(v_a_2878_);
lean_inc_ref(v___x_2924_);
lean_inc_ref(v_inst_2875_);
v___x_2925_ = lean_infer_type(v_inst_2875_, v___x_2924_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc_n(v_a_2926_, 2);
lean_dec_ref(v___x_2925_);
v___x_2927_ = lean_box(0);
v___x_2928_ = 0;
v___x_2929_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2926_, v___x_2927_, v___x_2928_, v___x_2924_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v_snd_2931_; lean_object* v_fst_2932_; lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v___x_2935_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v_snd_2931_ = lean_ctor_get(v_a_2930_, 1);
lean_inc(v_snd_2931_);
v_fst_2932_ = lean_ctor_get(v_a_2930_, 0);
lean_inc(v_fst_2932_);
lean_dec(v_a_2930_);
v_fst_2933_ = lean_ctor_get(v_snd_2931_, 0);
lean_inc(v_fst_2933_);
v_snd_2934_ = lean_ctor_get(v_snd_2931_, 1);
lean_inc(v_snd_2934_);
lean_dec(v_snd_2931_);
lean_inc(v_a_2880_);
lean_inc_ref(v_a_2879_);
lean_inc(v_a_2878_);
lean_inc_ref(v___x_2924_);
v___x_2935_ = lean_whnf(v_snd_2934_, v___x_2924_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___f_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
lean_inc(v_a_2926_);
v___f_2937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2937_, 0, v_a_2936_);
lean_closure_set(v___f_2937_, 1, v_fst_2932_);
lean_closure_set(v___f_2937_, 2, v_fst_2933_);
lean_closure_set(v___f_2937_, 3, v_inst_2875_);
lean_closure_set(v___f_2937_, 4, v_a_2926_);
lean_closure_set(v___f_2937_, 5, v_projInfo_x3f_2876_);
v___x_2938_ = 0;
v___x_2939_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2926_, v___f_2937_, v___x_2938_, v___x_2938_, v___x_2924_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec_ref(v___x_2924_);
return v___x_2939_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_fst_2933_);
lean_dec(v_fst_2932_);
lean_dec(v_a_2926_);
lean_dec_ref(v___x_2924_);
lean_dec(v_projInfo_x3f_2876_);
lean_dec_ref(v_inst_2875_);
v_a_2940_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2935_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2935_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_a_2926_);
lean_dec_ref(v___x_2924_);
lean_dec(v_projInfo_x3f_2876_);
lean_dec_ref(v_inst_2875_);
v_a_2948_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2929_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2929_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v___x_2924_);
lean_dec(v_projInfo_x3f_2876_);
lean_dec_ref(v_inst_2875_);
v_a_2956_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2925_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2925_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_2966_, lean_object* v_projInfo_x3f_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_2966_, v_projInfo_x3f_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_2974_, lean_object* v___x_2975_, lean_object* v_a_2976_, lean_object* v_inst_2977_, lean_object* v_R_2978_, lean_object* v_a_2979_, lean_object* v_b_2980_, lean_object* v_c_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2974_, v___x_2975_, v_a_2976_, v_a_2979_, v_b_2980_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_2988_, lean_object* v___x_2989_, lean_object* v_a_2990_, lean_object* v_inst_2991_, lean_object* v_R_2992_, lean_object* v_a_2993_, lean_object* v_b_2994_, lean_object* v_c_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_2988_, v___x_2989_, v_a_2990_, v_inst_2991_, v_R_2992_, v_a_2993_, v_b_2994_, v_c_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_a_2990_);
lean_dec(v___x_2989_);
lean_dec(v_upperBound_2988_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3010_, v_msg_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; lean_object* v_env_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = lean_st_ref_get(v___y_3019_);
v_env_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_ref(v_env_3022_);
lean_dec(v___x_3021_);
v___x_3023_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3022_, v_declName_3018_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3025_, v___y_3026_);
lean_dec(v___y_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3029_, v___y_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3043_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3049_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
lean_ctor_set(v___x_3049_, 2, v___x_3048_);
lean_ctor_set(v___x_3049_, 3, v___x_3048_);
lean_ctor_set(v___x_3049_, 4, v___x_3048_);
lean_ctor_set(v___x_3049_, 5, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3050_, lean_object* v_b_3051_, uint8_t v_kind_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_currNamespace_3057_; lean_object* v___x_3058_; lean_object* v_env_3059_; lean_object* v_nextMacroScope_3060_; lean_object* v_ngen_3061_; lean_object* v_auxDeclNGen_3062_; lean_object* v_traceState_3063_; lean_object* v_messages_3064_; lean_object* v_infoState_3065_; lean_object* v_snapshotTasks_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3093_; 
v_currNamespace_3057_ = lean_ctor_get(v___y_3054_, 6);
v___x_3058_ = lean_st_ref_take(v___y_3055_);
v_env_3059_ = lean_ctor_get(v___x_3058_, 0);
v_nextMacroScope_3060_ = lean_ctor_get(v___x_3058_, 1);
v_ngen_3061_ = lean_ctor_get(v___x_3058_, 2);
v_auxDeclNGen_3062_ = lean_ctor_get(v___x_3058_, 3);
v_traceState_3063_ = lean_ctor_get(v___x_3058_, 4);
v_messages_3064_ = lean_ctor_get(v___x_3058_, 6);
v_infoState_3065_ = lean_ctor_get(v___x_3058_, 7);
v_snapshotTasks_3066_ = lean_ctor_get(v___x_3058_, 8);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v___x_3058_, 5);
lean_dec(v_unused_3094_);
v___x_3068_ = v___x_3058_;
v_isShared_3069_ = v_isSharedCheck_3093_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_snapshotTasks_3066_);
lean_inc(v_infoState_3065_);
lean_inc(v_messages_3064_);
lean_inc(v_traceState_3063_);
lean_inc(v_auxDeclNGen_3062_);
lean_inc(v_ngen_3061_);
lean_inc(v_nextMacroScope_3060_);
lean_inc(v_env_3059_);
lean_dec(v___x_3058_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3093_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_inc(v_currNamespace_3057_);
v___x_3070_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3059_, v_ext_3050_, v_b_3051_, v_kind_3052_, v_currNamespace_3057_);
v___x_3071_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 5, v___x_3071_);
lean_ctor_set(v___x_3068_, 0, v___x_3070_);
v___x_3073_ = v___x_3068_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_nextMacroScope_3060_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_ngen_3061_);
lean_ctor_set(v_reuseFailAlloc_3092_, 3, v_auxDeclNGen_3062_);
lean_ctor_set(v_reuseFailAlloc_3092_, 4, v_traceState_3063_);
lean_ctor_set(v_reuseFailAlloc_3092_, 5, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3092_, 6, v_messages_3064_);
lean_ctor_set(v_reuseFailAlloc_3092_, 7, v_infoState_3065_);
lean_ctor_set(v_reuseFailAlloc_3092_, 8, v_snapshotTasks_3066_);
v___x_3073_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_mctx_3076_; lean_object* v_zetaDeltaFVarIds_3077_; lean_object* v_postponed_3078_; lean_object* v_diag_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3090_; 
v___x_3074_ = lean_st_ref_set(v___y_3055_, v___x_3073_);
v___x_3075_ = lean_st_ref_take(v___y_3053_);
v_mctx_3076_ = lean_ctor_get(v___x_3075_, 0);
v_zetaDeltaFVarIds_3077_ = lean_ctor_get(v___x_3075_, 2);
v_postponed_3078_ = lean_ctor_get(v___x_3075_, 3);
v_diag_3079_ = lean_ctor_get(v___x_3075_, 4);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3075_, 1);
lean_dec(v_unused_3091_);
v___x_3081_ = v___x_3075_;
v_isShared_3082_ = v_isSharedCheck_3090_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_diag_3079_);
lean_inc(v_postponed_3078_);
lean_inc(v_zetaDeltaFVarIds_3077_);
lean_inc(v_mctx_3076_);
lean_dec(v___x_3075_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3090_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3083_);
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_mctx_3076_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_zetaDeltaFVarIds_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_postponed_3078_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_diag_3079_);
v___x_3085_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_st_ref_set(v___y_3053_, v___x_3085_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3095_, lean_object* v_b_3096_, lean_object* v_kind_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
uint8_t v_kind_boxed_3102_; lean_object* v_res_3103_; 
v_kind_boxed_3102_ = lean_unbox(v_kind_3097_);
v_res_3103_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3095_, v_b_3096_, v_kind_boxed_3102_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3104_, lean_object* v_00_u03b2_3105_, lean_object* v_00_u03c3_3106_, lean_object* v_ext_3107_, lean_object* v_b_3108_, uint8_t v_kind_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3107_, v_b_3108_, v_kind_3109_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_00_u03c3_3118_, lean_object* v_ext_3119_, lean_object* v_b_3120_, lean_object* v_kind_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
uint8_t v_kind_boxed_3127_; lean_object* v_res_3128_; 
v_kind_boxed_3127_ = lean_unbox(v_kind_3121_);
v_res_3128_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3116_, v_00_u03b2_3117_, v_00_u03c3_3118_, v_ext_3119_, v_b_3120_, v_kind_boxed_3127_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; lean_object* v_env_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3132_ = lean_st_ref_get(v___y_3130_);
v_env_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc_ref(v_env_3133_);
lean_dec(v___x_3132_);
v___x_3134_ = lean_get_reducibility_status(v_env_3133_, v_declName_3129_);
v___x_3135_ = lean_box(v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3137_, v___y_3138_);
lean_dec(v___y_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3141_, v___y_3145_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3155_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__0);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
lean_ctor_set(v___x_3160_, 2, v___x_3159_);
lean_ctor_set(v___x_3160_, 3, v___x_3159_);
lean_ctor_set(v___x_3160_, 4, v___x_3158_);
lean_ctor_set(v___x_3160_, 5, v___x_3158_);
lean_ctor_set(v___x_3160_, 6, v___x_3158_);
lean_ctor_set(v___x_3160_, 7, v___x_3158_);
lean_ctor_set(v___x_3160_, 8, v___x_3158_);
lean_ctor_set(v___x_3160_, 9, v___x_3158_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_unsigned_to_nat(32u);
v___x_3162_ = lean_mk_empty_array_with_capacity(v___x_3161_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3164_ = ((size_t)5ULL);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_unsigned_to_nat(32u);
v___x_3167_ = lean_mk_empty_array_with_capacity(v___x_3166_);
v___x_3168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_3169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3167_);
lean_ctor_set(v___x_3169_, 2, v___x_3165_);
lean_ctor_set(v___x_3169_, 3, v___x_3165_);
lean_ctor_set_usize(v___x_3169_, 4, v___x_3164_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3170_ = lean_box(1);
v___x_3171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__4);
v___x_3172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__1);
v___x_3173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3170_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__6));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__8));
v___x_3179_ = l_Lean_stringToMessageData(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__10));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__12));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__14));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__16));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__18));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(lean_object* v_msg_3195_, lean_object* v_declHint_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v_env_3200_; uint8_t v___x_3201_; 
v___x_3199_ = lean_st_ref_get(v___y_3197_);
v_env_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3199_);
v___x_3201_ = l_Lean_Name_isAnonymous(v_declHint_3196_);
if (v___x_3201_ == 0)
{
uint8_t v_isExporting_3202_; 
v_isExporting_3202_ = lean_ctor_get_uint8(v_env_3200_, sizeof(void*)*8);
if (v_isExporting_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_msg_3195_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; uint8_t v___x_3205_; 
lean_inc_ref(v_env_3200_);
v___x_3204_ = l_Lean_Environment_setExporting(v_env_3200_, v___x_3201_);
lean_inc(v_declHint_3196_);
lean_inc_ref(v___x_3204_);
v___x_3205_ = l_Lean_Environment_contains(v___x_3204_, v_declHint_3196_, v_isExporting_3202_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v___x_3204_);
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_msg_3195_);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_c_3212_; lean_object* v___x_3213_; 
v___x_3207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
v___x_3209_ = l_Lean_Options_empty;
v___x_3210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3204_);
lean_ctor_set(v___x_3210_, 1, v___x_3207_);
lean_ctor_set(v___x_3210_, 2, v___x_3208_);
lean_ctor_set(v___x_3210_, 3, v___x_3209_);
lean_inc(v_declHint_3196_);
v___x_3211_ = l_Lean_MessageData_ofConstName(v_declHint_3196_, v___x_3201_);
v_c_3212_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3212_, 0, v___x_3210_);
lean_ctor_set(v_c_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3200_, v_declHint_3196_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v_c_3212_);
v___x_3216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__9);
v___x_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3215_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Lean_MessageData_note(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_msg_3195_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3256_; 
v_val_3221_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3223_ = v___x_3213_;
v_isShared_3224_ = v_isSharedCheck_3256_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_val_3221_);
lean_dec(v___x_3213_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3256_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_mod_3228_; uint8_t v___x_3229_; 
v___x_3225_ = lean_box(0);
v___x_3226_ = l_Lean_Environment_header(v_env_3200_);
lean_dec_ref(v_env_3200_);
v___x_3227_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3226_);
v_mod_3228_ = lean_array_get(v___x_3225_, v___x_3227_, v_val_3221_);
lean_dec(v_val_3221_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = l_Lean_isPrivateName(v_declHint_3196_);
lean_dec(v_declHint_3196_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__11);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v_c_3212_);
v___x_3232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__13);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_MessageData_ofName(v_mod_3228_);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__15);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_MessageData_note(v___x_3237_);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_msg_3195_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3239_);
v___x_3241_ = v___x_3223_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__7);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v_c_3212_);
v___x_3245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__17);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_MessageData_ofName(v_mod_3228_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__19);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_MessageData_note(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_msg_3195_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3252_);
v___x_3254_ = v___x_3223_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3257_; 
lean_dec_ref(v_env_3200_);
lean_dec(v_declHint_3196_);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_msg_3195_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_msg_3258_, lean_object* v_declHint_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3258_, v_declHint_3259_, v___y_3260_);
lean_dec(v___y_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_msg_3263_, lean_object* v_declHint_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3280_; 
v___x_3270_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3263_, v_declHint_3264_, v___y_3268_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3275_ = l_Lean_unknownIdentifierMessageTag;
v___x_3276_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v_a_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_3281_, lean_object* v_declHint_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3281_, v_declHint_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(lean_object* v_ref_3289_, lean_object* v_msg_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_fileName_3296_; lean_object* v_fileMap_3297_; lean_object* v_options_3298_; lean_object* v_currRecDepth_3299_; lean_object* v_maxRecDepth_3300_; lean_object* v_ref_3301_; lean_object* v_currNamespace_3302_; lean_object* v_openDecls_3303_; lean_object* v_initHeartbeats_3304_; lean_object* v_maxHeartbeats_3305_; lean_object* v_quotContext_3306_; lean_object* v_currMacroScope_3307_; uint8_t v_diag_3308_; lean_object* v_cancelTk_x3f_3309_; uint8_t v_suppressElabErrors_3310_; lean_object* v_inheritedTraceOptions_3311_; lean_object* v_ref_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_fileName_3296_ = lean_ctor_get(v___y_3293_, 0);
v_fileMap_3297_ = lean_ctor_get(v___y_3293_, 1);
v_options_3298_ = lean_ctor_get(v___y_3293_, 2);
v_currRecDepth_3299_ = lean_ctor_get(v___y_3293_, 3);
v_maxRecDepth_3300_ = lean_ctor_get(v___y_3293_, 4);
v_ref_3301_ = lean_ctor_get(v___y_3293_, 5);
v_currNamespace_3302_ = lean_ctor_get(v___y_3293_, 6);
v_openDecls_3303_ = lean_ctor_get(v___y_3293_, 7);
v_initHeartbeats_3304_ = lean_ctor_get(v___y_3293_, 8);
v_maxHeartbeats_3305_ = lean_ctor_get(v___y_3293_, 9);
v_quotContext_3306_ = lean_ctor_get(v___y_3293_, 10);
v_currMacroScope_3307_ = lean_ctor_get(v___y_3293_, 11);
v_diag_3308_ = lean_ctor_get_uint8(v___y_3293_, sizeof(void*)*14);
v_cancelTk_x3f_3309_ = lean_ctor_get(v___y_3293_, 12);
v_suppressElabErrors_3310_ = lean_ctor_get_uint8(v___y_3293_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3311_ = lean_ctor_get(v___y_3293_, 13);
v_ref_3312_ = l_Lean_replaceRef(v_ref_3289_, v_ref_3301_);
lean_inc_ref(v_inheritedTraceOptions_3311_);
lean_inc(v_cancelTk_x3f_3309_);
lean_inc(v_currMacroScope_3307_);
lean_inc(v_quotContext_3306_);
lean_inc(v_maxHeartbeats_3305_);
lean_inc(v_initHeartbeats_3304_);
lean_inc(v_openDecls_3303_);
lean_inc(v_currNamespace_3302_);
lean_inc(v_maxRecDepth_3300_);
lean_inc(v_currRecDepth_3299_);
lean_inc_ref(v_options_3298_);
lean_inc_ref(v_fileMap_3297_);
lean_inc_ref(v_fileName_3296_);
v___x_3313_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3313_, 0, v_fileName_3296_);
lean_ctor_set(v___x_3313_, 1, v_fileMap_3297_);
lean_ctor_set(v___x_3313_, 2, v_options_3298_);
lean_ctor_set(v___x_3313_, 3, v_currRecDepth_3299_);
lean_ctor_set(v___x_3313_, 4, v_maxRecDepth_3300_);
lean_ctor_set(v___x_3313_, 5, v_ref_3312_);
lean_ctor_set(v___x_3313_, 6, v_currNamespace_3302_);
lean_ctor_set(v___x_3313_, 7, v_openDecls_3303_);
lean_ctor_set(v___x_3313_, 8, v_initHeartbeats_3304_);
lean_ctor_set(v___x_3313_, 9, v_maxHeartbeats_3305_);
lean_ctor_set(v___x_3313_, 10, v_quotContext_3306_);
lean_ctor_set(v___x_3313_, 11, v_currMacroScope_3307_);
lean_ctor_set(v___x_3313_, 12, v_cancelTk_x3f_3309_);
lean_ctor_set(v___x_3313_, 13, v_inheritedTraceOptions_3311_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*14, v_diag_3308_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*14 + 1, v_suppressElabErrors_3310_);
v___x_3314_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3290_, v___y_3291_, v___y_3292_, v___x_3313_, v___y_3294_);
lean_dec_ref(v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3315_, lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3315_, v_msg_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v_ref_3315_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_ref_3323_, lean_object* v_msg_3324_, lean_object* v_declHint_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; lean_object* v_a_3332_; lean_object* v___x_3333_; 
v___x_3331_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11(v_msg_3324_, v_declHint_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3323_, v_a_3332_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_ref_3334_, lean_object* v_msg_3335_, lean_object* v_declHint_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3334_, v_msg_3335_, v_declHint_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v_ref_3334_);
return v_res_3342_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_3346_, lean_object* v_constName_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3353_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_3354_ = 0;
lean_inc(v_constName_3347_);
v___x_3355_ = l_Lean_MessageData_ofConstName(v_constName_3347_, v___x_3354_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3353_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3346_, v___x_3358_, v_constName_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_3360_, lean_object* v_constName_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3360_, v_constName_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v_ref_3360_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_ref_3374_; lean_object* v___x_3375_; 
v_ref_3374_ = lean_ctor_get(v___y_3371_, 5);
v___x_3375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3374_, v_constName_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v_env_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3389_ = lean_st_ref_get(v___y_3387_);
v_env_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_env_3390_);
lean_dec(v___x_3389_);
v___x_3391_ = 0;
lean_inc(v_constName_3383_);
v___x_3392_ = l_Lean_Environment_find_x3f(v_env_3390_, v_constName_3383_, v___x_3391_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3393_;
}
else
{
lean_object* v_val_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_constName_3383_);
v_val_3394_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3392_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_val_3394_);
lean_dec(v___x_3392_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 0);
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_val_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(uint8_t v___y_3416_, uint8_t v_suppressElabErrors_3417_, lean_object* v_x_3418_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 1)
{
lean_object* v_pre_3419_; 
v_pre_3419_ = lean_ctor_get(v_x_3418_, 0);
switch(lean_obj_tag(v_pre_3419_))
{
case 1:
{
lean_object* v_pre_3420_; 
v_pre_3420_ = lean_ctor_get(v_pre_3419_, 0);
switch(lean_obj_tag(v_pre_3420_))
{
case 0:
{
lean_object* v_str_3421_; lean_object* v_str_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v_str_3421_ = lean_ctor_get(v_x_3418_, 1);
v_str_3422_ = lean_ctor_get(v_pre_3419_, 1);
v___x_3423_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__0));
v___x_3424_ = lean_string_dec_eq(v_str_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__1));
v___x_3426_ = lean_string_dec_eq(v_str_3422_, v___x_3425_);
if (v___x_3426_ == 0)
{
return v___y_3416_;
}
else
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__2));
v___x_3428_ = lean_string_dec_eq(v_str_3421_, v___x_3427_);
if (v___x_3428_ == 0)
{
return v___y_3416_;
}
else
{
return v_suppressElabErrors_3417_;
}
}
}
else
{
lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__3));
v___x_3430_ = lean_string_dec_eq(v_str_3421_, v___x_3429_);
if (v___x_3430_ == 0)
{
return v___y_3416_;
}
else
{
return v_suppressElabErrors_3417_;
}
}
}
case 1:
{
lean_object* v_pre_3431_; 
v_pre_3431_ = lean_ctor_get(v_pre_3420_, 0);
if (lean_obj_tag(v_pre_3431_) == 0)
{
lean_object* v_str_3432_; lean_object* v_str_3433_; lean_object* v_str_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_str_3432_ = lean_ctor_get(v_x_3418_, 1);
v_str_3433_ = lean_ctor_get(v_pre_3419_, 1);
v_str_3434_ = lean_ctor_get(v_pre_3420_, 1);
v___x_3435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__4));
v___x_3436_ = lean_string_dec_eq(v_str_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
return v___y_3416_;
}
else
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__5));
v___x_3438_ = lean_string_dec_eq(v_str_3433_, v___x_3437_);
if (v___x_3438_ == 0)
{
return v___y_3416_;
}
else
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___closed__6));
v___x_3440_ = lean_string_dec_eq(v_str_3432_, v___x_3439_);
if (v___x_3440_ == 0)
{
return v___y_3416_;
}
else
{
return v_suppressElabErrors_3417_;
}
}
}
}
else
{
return v___y_3416_;
}
}
default: 
{
return v___y_3416_;
}
}
}
case 0:
{
lean_object* v_str_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
v_str_3441_ = lean_ctor_get(v_x_3418_, 1);
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3443_ = lean_string_dec_eq(v_str_3441_, v___x_3442_);
if (v___x_3443_ == 0)
{
return v___y_3416_;
}
else
{
return v_suppressElabErrors_3417_;
}
}
default: 
{
return v___y_3416_;
}
}
}
else
{
return v___y_3416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed(lean_object* v___y_3444_, lean_object* v_suppressElabErrors_3445_, lean_object* v_x_3446_){
_start:
{
uint8_t v___y_8288__boxed_3447_; uint8_t v_suppressElabErrors_boxed_3448_; uint8_t v_res_3449_; lean_object* v_r_3450_; 
v___y_8288__boxed_3447_ = lean_unbox(v___y_3444_);
v_suppressElabErrors_boxed_3448_ = lean_unbox(v_suppressElabErrors_3445_);
v_res_3449_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0(v___y_8288__boxed_3447_, v_suppressElabErrors_boxed_3448_, v_x_3446_);
lean_dec(v_x_3446_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(lean_object* v_ref_3451_, lean_object* v_msgData_3452_, uint8_t v_severity_3453_, uint8_t v_isSilent_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; uint8_t v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; uint8_t v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; uint8_t v___y_3539_; uint8_t v___x_3544_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; uint8_t v___y_3551_; uint8_t v___y_3552_; uint8_t v___y_3554_; uint8_t v___x_3569_; 
v___x_3544_ = 2;
v___x_3569_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3453_, v___x_3544_);
if (v___x_3569_ == 0)
{
v___y_3554_ = v___x_3569_;
goto v___jp_3553_;
}
else
{
uint8_t v___x_3570_; 
lean_inc_ref(v_msgData_3452_);
v___x_3570_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3452_);
v___y_3554_ = v___x_3570_;
goto v___jp_3553_;
}
v___jp_3460_:
{
lean_object* v___x_3470_; lean_object* v_currNamespace_3471_; lean_object* v_openDecls_3472_; lean_object* v_env_3473_; lean_object* v_nextMacroScope_3474_; lean_object* v_ngen_3475_; lean_object* v_auxDeclNGen_3476_; lean_object* v_traceState_3477_; lean_object* v_cache_3478_; lean_object* v_messages_3479_; lean_object* v_infoState_3480_; lean_object* v_snapshotTasks_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3495_; 
v___x_3470_ = lean_st_ref_take(v___y_3469_);
v_currNamespace_3471_ = lean_ctor_get(v___y_3468_, 6);
v_openDecls_3472_ = lean_ctor_get(v___y_3468_, 7);
v_env_3473_ = lean_ctor_get(v___x_3470_, 0);
v_nextMacroScope_3474_ = lean_ctor_get(v___x_3470_, 1);
v_ngen_3475_ = lean_ctor_get(v___x_3470_, 2);
v_auxDeclNGen_3476_ = lean_ctor_get(v___x_3470_, 3);
v_traceState_3477_ = lean_ctor_get(v___x_3470_, 4);
v_cache_3478_ = lean_ctor_get(v___x_3470_, 5);
v_messages_3479_ = lean_ctor_get(v___x_3470_, 6);
v_infoState_3480_ = lean_ctor_get(v___x_3470_, 7);
v_snapshotTasks_3481_ = lean_ctor_get(v___x_3470_, 8);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3483_ = v___x_3470_;
v_isShared_3484_ = v_isSharedCheck_3495_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_snapshotTasks_3481_);
lean_inc(v_infoState_3480_);
lean_inc(v_messages_3479_);
lean_inc(v_cache_3478_);
lean_inc(v_traceState_3477_);
lean_inc(v_auxDeclNGen_3476_);
lean_inc(v_ngen_3475_);
lean_inc(v_nextMacroScope_3474_);
lean_inc(v_env_3473_);
lean_dec(v___x_3470_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3495_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_inc(v_openDecls_3472_);
lean_inc(v_currNamespace_3471_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_currNamespace_3471_);
lean_ctor_set(v___x_3485_, 1, v_openDecls_3472_);
v___x_3486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___y_3464_);
lean_inc_ref(v___y_3462_);
lean_inc_ref(v___y_3463_);
v___x_3487_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3487_, 0, v___y_3463_);
lean_ctor_set(v___x_3487_, 1, v___y_3465_);
lean_ctor_set(v___x_3487_, 2, v___y_3467_);
lean_ctor_set(v___x_3487_, 3, v___y_3462_);
lean_ctor_set(v___x_3487_, 4, v___x_3486_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*5, v___y_3461_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*5 + 1, v___y_3466_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*5 + 2, v_isSilent_3454_);
v___x_3488_ = l_Lean_MessageLog_add(v___x_3487_, v_messages_3479_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 6, v___x_3488_);
v___x_3490_ = v___x_3483_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_env_3473_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_nextMacroScope_3474_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_ngen_3475_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_auxDeclNGen_3476_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_traceState_3477_);
lean_ctor_set(v_reuseFailAlloc_3494_, 5, v_cache_3478_);
lean_ctor_set(v_reuseFailAlloc_3494_, 6, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3494_, 7, v_infoState_3480_);
lean_ctor_set(v_reuseFailAlloc_3494_, 8, v_snapshotTasks_3481_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = lean_st_ref_set(v___y_3469_, v___x_3490_);
v___x_3492_ = lean_box(0);
v___x_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
return v___x_3493_;
}
}
}
v___jp_3496_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3520_; 
v___x_3505_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3452_);
v___x_3506_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3505_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_inc_ref_n(v___y_3502_, 2);
v___x_3511_ = l_Lean_FileMap_toPosition(v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
v___x_3512_ = l_Lean_FileMap_toPosition(v___y_3502_, v___y_3504_);
lean_dec(v___y_3504_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
v___x_3514_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___closed__0));
if (v___y_3500_ == 0)
{
lean_del_object(v___x_3509_);
lean_dec_ref(v___y_3497_);
v___y_3461_ = v___y_3498_;
v___y_3462_ = v___x_3514_;
v___y_3463_ = v___y_3499_;
v___y_3464_ = v_a_3507_;
v___y_3465_ = v___x_3511_;
v___y_3466_ = v___y_3501_;
v___y_3467_ = v___x_3513_;
v___y_3468_ = v___y_3457_;
v___y_3469_ = v___y_3458_;
goto v___jp_3460_;
}
else
{
uint8_t v___x_3515_; 
lean_inc(v_a_3507_);
v___x_3515_ = l_Lean_MessageData_hasTag(v___y_3497_, v_a_3507_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec_ref(v___x_3513_);
lean_dec_ref(v___x_3511_);
lean_dec(v_a_3507_);
v___x_3516_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3516_);
v___x_3518_ = v___x_3509_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
else
{
lean_del_object(v___x_3509_);
v___y_3461_ = v___y_3498_;
v___y_3462_ = v___x_3514_;
v___y_3463_ = v___y_3499_;
v___y_3464_ = v_a_3507_;
v___y_3465_ = v___x_3511_;
v___y_3466_ = v___y_3501_;
v___y_3467_ = v___x_3513_;
v___y_3468_ = v___y_3457_;
v___y_3469_ = v___y_3458_;
goto v___jp_3460_;
}
}
}
}
v___jp_3521_:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_Syntax_getTailPos_x3f(v___y_3525_, v___y_3523_);
lean_dec(v___y_3525_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_inc(v___y_3529_);
v___y_3497_ = v___y_3522_;
v___y_3498_ = v___y_3523_;
v___y_3499_ = v___y_3524_;
v___y_3500_ = v___y_3527_;
v___y_3501_ = v___y_3526_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3529_;
goto v___jp_3496_;
}
else
{
lean_object* v_val_3531_; 
v_val_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_val_3531_);
lean_dec_ref(v___x_3530_);
v___y_3497_ = v___y_3522_;
v___y_3498_ = v___y_3523_;
v___y_3499_ = v___y_3524_;
v___y_3500_ = v___y_3527_;
v___y_3501_ = v___y_3526_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v_val_3531_;
goto v___jp_3496_;
}
}
v___jp_3532_:
{
lean_object* v_ref_3540_; lean_object* v___x_3541_; 
v_ref_3540_ = l_Lean_replaceRef(v_ref_3451_, v___y_3538_);
v___x_3541_ = l_Lean_Syntax_getPos_x3f(v_ref_3540_, v___y_3534_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_unsigned_to_nat(0u);
v___y_3522_ = v___y_3533_;
v___y_3523_ = v___y_3534_;
v___y_3524_ = v___y_3535_;
v___y_3525_ = v_ref_3540_;
v___y_3526_ = v___y_3539_;
v___y_3527_ = v___y_3536_;
v___y_3528_ = v___y_3537_;
v___y_3529_ = v___x_3542_;
goto v___jp_3521_;
}
else
{
lean_object* v_val_3543_; 
v_val_3543_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_val_3543_);
lean_dec_ref(v___x_3541_);
v___y_3522_ = v___y_3533_;
v___y_3523_ = v___y_3534_;
v___y_3524_ = v___y_3535_;
v___y_3525_ = v_ref_3540_;
v___y_3526_ = v___y_3539_;
v___y_3527_ = v___y_3536_;
v___y_3528_ = v___y_3537_;
v___y_3529_ = v_val_3543_;
goto v___jp_3521_;
}
}
v___jp_3545_:
{
if (v___y_3552_ == 0)
{
v___y_3533_ = v___y_3547_;
v___y_3534_ = v___y_3551_;
v___y_3535_ = v___y_3546_;
v___y_3536_ = v___y_3548_;
v___y_3537_ = v___y_3549_;
v___y_3538_ = v___y_3550_;
v___y_3539_ = v_severity_3453_;
goto v___jp_3532_;
}
else
{
v___y_3533_ = v___y_3547_;
v___y_3534_ = v___y_3551_;
v___y_3535_ = v___y_3546_;
v___y_3536_ = v___y_3548_;
v___y_3537_ = v___y_3549_;
v___y_3538_ = v___y_3550_;
v___y_3539_ = v___x_3544_;
goto v___jp_3532_;
}
}
v___jp_3553_:
{
if (v___y_3554_ == 0)
{
lean_object* v_fileName_3555_; lean_object* v_fileMap_3556_; lean_object* v_options_3557_; lean_object* v_ref_3558_; uint8_t v_suppressElabErrors_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___f_3562_; uint8_t v___x_3563_; uint8_t v___x_3564_; 
v_fileName_3555_ = lean_ctor_get(v___y_3457_, 0);
v_fileMap_3556_ = lean_ctor_get(v___y_3457_, 1);
v_options_3557_ = lean_ctor_get(v___y_3457_, 2);
v_ref_3558_ = lean_ctor_get(v___y_3457_, 5);
v_suppressElabErrors_3559_ = lean_ctor_get_uint8(v___y_3457_, sizeof(void*)*14 + 1);
v___x_3560_ = lean_box(v___y_3554_);
v___x_3561_ = lean_box(v_suppressElabErrors_3559_);
v___f_3562_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3562_, 0, v___x_3560_);
lean_closure_set(v___f_3562_, 1, v___x_3561_);
v___x_3563_ = 1;
v___x_3564_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3453_, v___x_3563_);
if (v___x_3564_ == 0)
{
v___y_3546_ = v_fileName_3555_;
v___y_3547_ = v___f_3562_;
v___y_3548_ = v_suppressElabErrors_3559_;
v___y_3549_ = v_fileMap_3556_;
v___y_3550_ = v_ref_3558_;
v___y_3551_ = v___y_3554_;
v___y_3552_ = v___x_3564_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = l_Lean_warningAsError;
v___x_3566_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3557_, v___x_3565_);
v___y_3546_ = v_fileName_3555_;
v___y_3547_ = v___f_3562_;
v___y_3548_ = v_suppressElabErrors_3559_;
v___y_3549_ = v_fileMap_3556_;
v___y_3550_ = v_ref_3558_;
v___y_3551_ = v___y_3554_;
v___y_3552_ = v___x_3566_;
goto v___jp_3545_;
}
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec_ref(v_msgData_3452_);
v___x_3567_ = lean_box(0);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10___boxed(lean_object* v_ref_3571_, lean_object* v_msgData_3572_, lean_object* v_severity_3573_, lean_object* v_isSilent_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v_severity_boxed_3580_; uint8_t v_isSilent_boxed_3581_; lean_object* v_res_3582_; 
v_severity_boxed_3580_ = lean_unbox(v_severity_3573_);
v_isSilent_boxed_3581_ = lean_unbox(v_isSilent_3574_);
v_res_3582_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3571_, v_msgData_3572_, v_severity_boxed_3580_, v_isSilent_boxed_3581_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v_ref_3571_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(lean_object* v_msgData_3583_, uint8_t v_severity_3584_, uint8_t v_isSilent_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_ref_3591_; lean_object* v___x_3592_; 
v_ref_3591_ = lean_ctor_get(v___y_3588_, 5);
v___x_3592_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8_spec__10(v_ref_3591_, v_msgData_3583_, v_severity_3584_, v_isSilent_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8___boxed(lean_object* v_msgData_3593_, lean_object* v_severity_3594_, lean_object* v_isSilent_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v_severity_boxed_3601_; uint8_t v_isSilent_boxed_3602_; lean_object* v_res_3603_; 
v_severity_boxed_3601_ = lean_unbox(v_severity_3594_);
v_isSilent_boxed_3602_ = lean_unbox(v_isSilent_3595_);
v_res_3603_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3593_, v_severity_boxed_3601_, v_isSilent_boxed_3602_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(lean_object* v_msgData_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
uint8_t v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = 1;
v___x_3611_ = 0;
v___x_3612_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_addInstance_spec__5_spec__8(v_msgData_3604_, v___x_3610_, v___x_3611_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5___boxed(lean_object* v_msgData_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v_msgData_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v_env_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; 
v___x_3626_ = lean_st_ref_get(v___y_3624_);
v_env_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc_ref(v_env_3627_);
lean_dec(v___x_3626_);
v___x_3628_ = 0;
lean_inc(v_constName_3620_);
v___x_3629_ = l_Lean_Environment_findConstVal_x3f(v_env_3627_, v_constName_3620_, v___x_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
return v___x_3630_;
}
else
{
lean_object* v_val_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_constName_3620_);
v_val_3631_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3629_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_val_3631_);
lean_dec(v___x_3629_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 0);
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_val_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
if (lean_obj_tag(v_a_3646_) == 0)
{
lean_object* v___x_3648_; 
v___x_3648_ = l_List_reverse___redArg(v_a_3647_);
return v___x_3648_;
}
else
{
lean_object* v_head_3649_; lean_object* v_tail_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3659_; 
v_head_3649_ = lean_ctor_get(v_a_3646_, 0);
v_tail_3650_ = lean_ctor_get(v_a_3646_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3646_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3652_ = v_a_3646_;
v_isShared_3653_ = v_isSharedCheck_3659_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_tail_3650_);
lean_inc(v_head_3649_);
lean_dec(v_a_3646_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3659_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = l_Lean_mkLevelParam(v_head_3649_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v_a_3647_);
lean_ctor_set(v___x_3652_, 0, v___x_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_a_3647_);
v___x_3656_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
v_a_3646_ = v_tail_3650_;
v_a_3647_ = v___x_3656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v___x_3666_; 
lean_inc(v_constName_3660_);
v___x_3666_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3678_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3678_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3678_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_levelParams_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_levelParams_3671_ = lean_ctor_get(v_a_3667_, 1);
lean_inc(v_levelParams_3671_);
lean_dec(v_a_3667_);
v___x_3672_ = lean_box(0);
v___x_3673_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_3671_, v___x_3672_);
v___x_3674_ = l_Lean_mkConst(v_constName_3660_, v___x_3673_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3674_);
v___x_3676_ = v___x_3669_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_constName_3660_);
v_a_3679_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3666_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3666_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3693_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
return v___x_3696_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_3703_, uint8_t v_attrKind_3704_, lean_object* v_prio_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___x_3711_; 
lean_inc(v_declName_3703_);
v___x_3711_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_3703_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc_n(v_a_3712_, 2);
lean_dec_ref(v___x_3711_);
v___x_3713_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_3712_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___x_3742_; lean_object* v_a_3743_; uint8_t v___x_3744_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v___x_3713_);
lean_inc(v_declName_3703_);
v___x_3742_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3703_, v_a_3709_);
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref(v___x_3742_);
v___x_3744_ = lean_unbox(v_a_3743_);
lean_dec(v_a_3743_);
switch(v___x_3744_)
{
case 0:
{
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3715_;
}
case 3:
{
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3715_;
}
default: 
{
lean_object* v___x_3745_; 
lean_inc(v_declName_3703_);
v___x_3745_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_3703_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; uint8_t v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref(v___x_3745_);
v___x_3747_ = l_Lean_ConstantInfo_isDefinition(v_a_3746_);
lean_dec(v_a_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v_env_3749_; uint8_t v___x_3750_; 
v___x_3748_ = lean_st_ref_get(v_a_3709_);
v_env_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc_ref(v_env_3749_);
lean_dec(v___x_3748_);
lean_inc(v_declName_3703_);
v___x_3750_ = l_Lean_wasOriginallyDefn(v_env_3749_, v_declName_3703_);
if (v___x_3750_ == 0)
{
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3751_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3703_);
v___x_3752_ = l_Lean_MessageData_ofName(v_declName_3703_);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3755_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_dec_ref(v___x_3756_);
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3715_;
}
else
{
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
return v___x_3756_;
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3757_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_3703_);
v___x_3758_ = l_Lean_MessageData_ofName(v_declName_3703_);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_logWarning___at___00Lean_Meta_addInstance_spec__5(v___x_3761_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref(v___x_3762_);
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3715_;
}
else
{
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
return v___x_3762_;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
v_a_3763_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3745_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3745_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
v___jp_3715_:
{
lean_object* v___x_3720_; lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3741_; 
lean_inc(v_declName_3703_);
v___x_3720_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3703_, v___y_3719_);
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3741_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3741_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; 
lean_inc(v_a_3712_);
v___x_3725_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_3712_, v_a_3721_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref(v___x_3725_);
v___x_3727_ = l_Lean_Meta_instanceExtension;
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 1);
lean_ctor_set(v___x_3723_, 0, v_declName_3703_);
v___x_3729_ = v___x_3723_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_declName_3703_);
v___x_3729_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3730_, 0, v_a_3714_);
lean_ctor_set(v___x_3730_, 1, v_a_3712_);
lean_ctor_set(v___x_3730_, 2, v_prio_3705_);
lean_ctor_set(v___x_3730_, 3, v___x_3729_);
lean_ctor_set(v___x_3730_, 4, v_a_3726_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*5, v_attrKind_3704_);
v___x_3731_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_3727_, v___x_3730_, v_attrKind_3704_, v___y_3717_, v___y_3718_, v___y_3719_);
return v___x_3731_;
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3723_);
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
v_a_3733_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3725_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3725_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_a_3712_);
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
v_a_3771_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3713_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3713_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec(v_prio_3705_);
lean_dec(v_declName_3703_);
v_a_3779_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3711_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3711_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_3787_, lean_object* v_attrKind_3788_, lean_object* v_prio_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
uint8_t v_attrKind_boxed_3795_; lean_object* v_res_3796_; 
v_attrKind_boxed_3795_ = lean_unbox(v_attrKind_3788_);
v_res_3796_ = l_Lean_Meta_addInstance(v_declName_3787_, v_attrKind_boxed_3795_, v_prio_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_3797_, lean_object* v_constName_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3805_, lean_object* v_constName_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_3805_, v_constName_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_3813_, lean_object* v_ref_3814_, lean_object* v_constName_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_3814_, v_constName_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_3822_, lean_object* v_ref_3823_, lean_object* v_constName_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_3822_, v_ref_3823_, v_constName_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v_ref_3823_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_3831_, lean_object* v_ref_3832_, lean_object* v_msg_3833_, lean_object* v_declHint_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___redArg(v_ref_3832_, v_msg_3833_, v_declHint_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_ref_3842_, lean_object* v_msg_3843_, lean_object* v_declHint_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9(v_00_u03b1_3841_, v_ref_3842_, v_msg_3843_, v_declHint_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v_ref_3842_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(lean_object* v_msg_3851_, lean_object* v_declHint_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg(v_msg_3851_, v_declHint_3852_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___boxed(lean_object* v_msg_3859_, lean_object* v_declHint_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13(v_msg_3859_, v_declHint_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_3867_, lean_object* v_ref_3868_, lean_object* v_msg_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___redArg(v_ref_3868_, v_msg_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3876_, lean_object* v_ref_3877_, lean_object* v_msg_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__12(v_00_u03b1_3876_, v_ref_3877_, v_msg_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v_ref_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_3885_, uint8_t v_s_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; lean_object* v_env_3891_; lean_object* v_nextMacroScope_3892_; lean_object* v_ngen_3893_; lean_object* v_auxDeclNGen_3894_; lean_object* v_traceState_3895_; lean_object* v_messages_3896_; lean_object* v_infoState_3897_; lean_object* v_snapshotTasks_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3927_; 
v___x_3890_ = lean_st_ref_take(v___y_3888_);
v_env_3891_ = lean_ctor_get(v___x_3890_, 0);
v_nextMacroScope_3892_ = lean_ctor_get(v___x_3890_, 1);
v_ngen_3893_ = lean_ctor_get(v___x_3890_, 2);
v_auxDeclNGen_3894_ = lean_ctor_get(v___x_3890_, 3);
v_traceState_3895_ = lean_ctor_get(v___x_3890_, 4);
v_messages_3896_ = lean_ctor_get(v___x_3890_, 6);
v_infoState_3897_ = lean_ctor_get(v___x_3890_, 7);
v_snapshotTasks_3898_ = lean_ctor_get(v___x_3890_, 8);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v___x_3890_, 5);
lean_dec(v_unused_3928_);
v___x_3900_ = v___x_3890_;
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_snapshotTasks_3898_);
lean_inc(v_infoState_3897_);
lean_inc(v_messages_3896_);
lean_inc(v_traceState_3895_);
lean_inc(v_auxDeclNGen_3894_);
lean_inc(v_ngen_3893_);
lean_inc(v_nextMacroScope_3892_);
lean_inc(v_env_3891_);
lean_dec(v___x_3890_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3902_ = 0;
v___x_3903_ = lean_box(0);
v___x_3904_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_3891_, v_declName_3885_, v_s_3886_, v___x_3902_, v___x_3903_);
v___x_3905_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 5, v___x_3905_);
lean_ctor_set(v___x_3900_, 0, v___x_3904_);
v___x_3907_ = v___x_3900_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_nextMacroScope_3892_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_ngen_3893_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_auxDeclNGen_3894_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v_traceState_3895_);
lean_ctor_set(v_reuseFailAlloc_3926_, 5, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3926_, 6, v_messages_3896_);
lean_ctor_set(v_reuseFailAlloc_3926_, 7, v_infoState_3897_);
lean_ctor_set(v_reuseFailAlloc_3926_, 8, v_snapshotTasks_3898_);
v___x_3907_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v_mctx_3910_; lean_object* v_zetaDeltaFVarIds_3911_; lean_object* v_postponed_3912_; lean_object* v_diag_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3924_; 
v___x_3908_ = lean_st_ref_set(v___y_3888_, v___x_3907_);
v___x_3909_ = lean_st_ref_take(v___y_3887_);
v_mctx_3910_ = lean_ctor_get(v___x_3909_, 0);
v_zetaDeltaFVarIds_3911_ = lean_ctor_get(v___x_3909_, 2);
v_postponed_3912_ = lean_ctor_get(v___x_3909_, 3);
v_diag_3913_ = lean_ctor_get(v___x_3909_, 4);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v___x_3909_, 1);
lean_dec(v_unused_3925_);
v___x_3915_ = v___x_3909_;
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_diag_3913_);
lean_inc(v_postponed_3912_);
lean_inc(v_zetaDeltaFVarIds_3911_);
lean_inc(v_mctx_3910_);
lean_dec(v___x_3909_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 1, v___x_3917_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_mctx_3910_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_zetaDeltaFVarIds_3911_);
lean_ctor_set(v_reuseFailAlloc_3923_, 3, v_postponed_3912_);
lean_ctor_set(v_reuseFailAlloc_3923_, 4, v_diag_3913_);
v___x_3919_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_st_ref_set(v___y_3887_, v___x_3919_);
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_3929_, lean_object* v_s_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v_s_boxed_3934_; lean_object* v_res_3935_; 
v_s_boxed_3934_ = lean_unbox(v_s_3930_);
v_res_3935_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3929_, v_s_boxed_3934_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_3936_, uint8_t v_s_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3936_, v_s_3937_, v___y_3939_, v___y_3941_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_3944_, lean_object* v_s_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v_s_boxed_3951_; lean_object* v_res_3952_; 
v_s_boxed_3951_ = lean_unbox(v_s_3945_);
v_res_3952_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_3944_, v_s_boxed_3951_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_3953_, uint8_t v_attrKind_3954_, lean_object* v_prio_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = 3;
lean_inc(v_declName_3953_);
v___x_3962_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_3953_, v___x_3961_, v_a_3957_, v_a_3959_);
lean_dec_ref(v___x_3962_);
v___x_3963_ = l_Lean_Meta_addInstance(v_declName_3953_, v_attrKind_3954_, v_prio_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_3964_, lean_object* v_attrKind_3965_, lean_object* v_prio_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
uint8_t v_attrKind_boxed_3972_; lean_object* v_res_3973_; 
v_attrKind_boxed_3972_ = lean_unbox(v_attrKind_3965_);
v_res_3973_ = l_Lean_Meta_registerInstance(v_declName_3964_, v_attrKind_boxed_3972_, v_prio_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_3974_, lean_object* v_x_3975_){
_start:
{
lean_inc_ref(v_a_3974_);
return v_a_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_3976_, lean_object* v_x_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_3976_, v_x_3977_);
lean_dec_ref(v_x_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; lean_object* v_env_3984_; lean_object* v_options_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3983_ = lean_st_ref_get(v___y_3981_);
v_env_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc_ref(v_env_3984_);
lean_dec(v___x_3983_);
v_options_3985_ = lean_ctor_get(v___y_3980_, 2);
v___x_3986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__2);
v___x_3987_ = lean_unsigned_to_nat(32u);
v___x_3988_ = lean_mk_empty_array_with_capacity(v___x_3987_);
lean_dec_ref(v___x_3988_);
v___x_3989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3985_);
v___x_3990_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3990_, 0, v_env_3984_);
lean_ctor_set(v___x_3990_, 1, v___x_3986_);
lean_ctor_set(v___x_3990_, 2, v___x_3989_);
lean_ctor_set(v___x_3990_, 3, v_options_3985_);
v___x_3991_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v_msgData_3979_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_ref_4002_; lean_object* v___x_4003_; lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4012_; 
v_ref_4002_ = lean_ctor_get(v___y_3999_, 5);
v___x_4003_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_3998_, v___y_3999_, v___y_4000_);
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4006_ = v___x_4003_;
v_isShared_4007_ = v_isSharedCheck_4012_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4012_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4010_; 
lean_inc(v_ref_4002_);
v___x_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4008_, 0, v_ref_4002_);
lean_ctor_set(v___x_4008_, 1, v_a_4004_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 1);
lean_ctor_set(v___x_4006_, 0, v___x_4008_);
v___x_4010_ = v___x_4006_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
return v_res_4017_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4018_, lean_object* v_i_4019_, lean_object* v_k_4020_){
_start:
{
lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4021_ = lean_array_get_size(v_keys_4018_);
v___x_4022_ = lean_nat_dec_lt(v_i_4019_, v___x_4021_);
if (v___x_4022_ == 0)
{
lean_dec(v_i_4019_);
return v___x_4022_;
}
else
{
lean_object* v_k_x27_4023_; uint8_t v___x_4024_; 
v_k_x27_4023_ = lean_array_fget_borrowed(v_keys_4018_, v_i_4019_);
v___x_4024_ = lean_name_eq(v_k_4020_, v_k_x27_4023_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_nat_add(v_i_4019_, v___x_4025_);
lean_dec(v_i_4019_);
v_i_4019_ = v___x_4026_;
goto _start;
}
else
{
lean_dec(v_i_4019_);
return v___x_4024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4028_, lean_object* v_i_4029_, lean_object* v_k_4030_){
_start:
{
uint8_t v_res_4031_; lean_object* v_r_4032_; 
v_res_4031_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4028_, v_i_4029_, v_k_4030_);
lean_dec(v_k_4030_);
lean_dec_ref(v_keys_4028_);
v_r_4032_ = lean_box(v_res_4031_);
return v_r_4032_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4033_, size_t v_x_4034_, lean_object* v_x_4035_){
_start:
{
if (lean_obj_tag(v_x_4033_) == 0)
{
lean_object* v_es_4036_; lean_object* v___x_4037_; size_t v___x_4038_; size_t v___x_4039_; size_t v___x_4040_; lean_object* v_j_4041_; lean_object* v___x_4042_; 
v_es_4036_ = lean_ctor_get(v_x_4033_, 0);
v___x_4037_ = lean_box(2);
v___x_4038_ = ((size_t)5ULL);
v___x_4039_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4040_ = lean_usize_land(v_x_4034_, v___x_4039_);
v_j_4041_ = lean_usize_to_nat(v___x_4040_);
v___x_4042_ = lean_array_get_borrowed(v___x_4037_, v_es_4036_, v_j_4041_);
lean_dec(v_j_4041_);
switch(lean_obj_tag(v___x_4042_))
{
case 0:
{
lean_object* v_key_4043_; uint8_t v___x_4044_; 
v_key_4043_ = lean_ctor_get(v___x_4042_, 0);
v___x_4044_ = lean_name_eq(v_x_4035_, v_key_4043_);
return v___x_4044_;
}
case 1:
{
lean_object* v_node_4045_; size_t v___x_4046_; 
v_node_4045_ = lean_ctor_get(v___x_4042_, 0);
v___x_4046_ = lean_usize_shift_right(v_x_4034_, v___x_4038_);
v_x_4033_ = v_node_4045_;
v_x_4034_ = v___x_4046_;
goto _start;
}
default: 
{
uint8_t v___x_4048_; 
v___x_4048_ = 0;
return v___x_4048_;
}
}
}
else
{
lean_object* v_ks_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v_ks_4049_ = lean_ctor_get(v_x_4033_, 0);
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4049_, v___x_4050_, v_x_4035_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4052_, lean_object* v_x_4053_, lean_object* v_x_4054_){
_start:
{
size_t v_x_2353__boxed_4055_; uint8_t v_res_4056_; lean_object* v_r_4057_; 
v_x_2353__boxed_4055_ = lean_unbox_usize(v_x_4053_);
lean_dec(v_x_4053_);
v_res_4056_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4052_, v_x_2353__boxed_4055_, v_x_4054_);
lean_dec(v_x_4054_);
lean_dec_ref(v_x_4052_);
v_r_4057_ = lean_box(v_res_4056_);
return v_r_4057_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4058_, lean_object* v_x_4059_){
_start:
{
uint64_t v___y_4061_; 
if (lean_obj_tag(v_x_4059_) == 0)
{
uint64_t v___x_4064_; 
v___x_4064_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4061_ = v___x_4064_;
goto v___jp_4060_;
}
else
{
uint64_t v_hash_4065_; 
v_hash_4065_ = lean_ctor_get_uint64(v_x_4059_, sizeof(void*)*2);
v___y_4061_ = v_hash_4065_;
goto v___jp_4060_;
}
v___jp_4060_:
{
size_t v___x_4062_; uint8_t v___x_4063_; 
v___x_4062_ = lean_uint64_to_usize(v___y_4061_);
v___x_4063_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4058_, v___x_4062_, v_x_4059_);
return v___x_4063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4066_, lean_object* v_x_4067_){
_start:
{
uint8_t v_res_4068_; lean_object* v_r_4069_; 
v_res_4068_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4066_, v_x_4067_);
lean_dec(v_x_4067_);
lean_dec_ref(v_x_4066_);
v_r_4069_ = lean_box(v_res_4068_);
return v_r_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4070_, lean_object* v_declName_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_instanceNames_4078_; uint8_t v___x_4079_; 
v_instanceNames_4078_ = lean_ctor_get(v_d_4070_, 1);
v___x_4079_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4078_, v_declName_4071_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v_d_4070_);
v___x_4080_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4081_ = l_Lean_MessageData_ofConstName(v_declName_4071_, v___x_4079_);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4082_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4084_, v___y_4072_, v___y_4073_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4085_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4085_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
else
{
goto v___jp_4075_;
}
v___jp_4075_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = l_Lean_Meta_Instances_eraseCore(v_d_4070_, v_declName_4071_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4094_, lean_object* v_declName_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4094_, v_declName_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4100_, lean_object* v_declName_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___x_4105_; lean_object* v_env_4106_; lean_object* v___x_4107_; lean_object* v_ext_4108_; lean_object* v_toEnvExtension_4109_; lean_object* v_asyncMode_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4105_ = lean_st_ref_get(v___y_4103_);
v_env_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc_ref(v_env_4106_);
lean_dec(v___x_4105_);
v___x_4107_ = l_Lean_Meta_instanceExtension;
v_ext_4108_ = lean_ctor_get(v___x_4107_, 1);
v_toEnvExtension_4109_ = lean_ctor_get(v_ext_4108_, 0);
v_asyncMode_4110_ = lean_ctor_get(v_toEnvExtension_4109_, 2);
v___x_4111_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4100_, v___x_4107_, v_env_4106_, v_asyncMode_4110_);
v___x_4112_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4111_, v_declName_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4142_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4142_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4142_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v_env_4118_; lean_object* v_nextMacroScope_4119_; lean_object* v_ngen_4120_; lean_object* v_auxDeclNGen_4121_; lean_object* v_traceState_4122_; lean_object* v_messages_4123_; lean_object* v_infoState_4124_; lean_object* v_snapshotTasks_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4140_; 
v___x_4117_ = lean_st_ref_take(v___y_4103_);
v_env_4118_ = lean_ctor_get(v___x_4117_, 0);
v_nextMacroScope_4119_ = lean_ctor_get(v___x_4117_, 1);
v_ngen_4120_ = lean_ctor_get(v___x_4117_, 2);
v_auxDeclNGen_4121_ = lean_ctor_get(v___x_4117_, 3);
v_traceState_4122_ = lean_ctor_get(v___x_4117_, 4);
v_messages_4123_ = lean_ctor_get(v___x_4117_, 6);
v_infoState_4124_ = lean_ctor_get(v___x_4117_, 7);
v_snapshotTasks_4125_ = lean_ctor_get(v___x_4117_, 8);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v___x_4117_, 5);
lean_dec(v_unused_4141_);
v___x_4127_ = v___x_4117_;
v_isShared_4128_ = v_isSharedCheck_4140_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_snapshotTasks_4125_);
lean_inc(v_infoState_4124_);
lean_inc(v_messages_4123_);
lean_inc(v_traceState_4122_);
lean_inc(v_auxDeclNGen_4121_);
lean_inc(v_ngen_4120_);
lean_inc(v_nextMacroScope_4119_);
lean_inc(v_env_4118_);
lean_dec(v___x_4117_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4140_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___f_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___f_4129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4129_, 0, v_a_4113_);
v___x_4130_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4107_, v_env_4118_, v___f_4129_);
v___x_4131_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 5, v___x_4131_);
lean_ctor_set(v___x_4127_, 0, v___x_4130_);
v___x_4133_ = v___x_4127_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_nextMacroScope_4119_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_ngen_4120_);
lean_ctor_set(v_reuseFailAlloc_4139_, 3, v_auxDeclNGen_4121_);
lean_ctor_set(v_reuseFailAlloc_4139_, 4, v_traceState_4122_);
lean_ctor_set(v_reuseFailAlloc_4139_, 5, v___x_4131_);
lean_ctor_set(v_reuseFailAlloc_4139_, 6, v_messages_4123_);
lean_ctor_set(v_reuseFailAlloc_4139_, 7, v_infoState_4124_);
lean_ctor_set(v_reuseFailAlloc_4139_, 8, v_snapshotTasks_4125_);
v___x_4133_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4134_ = lean_st_ref_set(v___y_4103_, v___x_4133_);
v___x_4135_ = lean_box(0);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4135_);
v___x_4137_ = v___x_4115_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_a_4143_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4112_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4112_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4151_, lean_object* v_declName_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4151_, v_declName_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___x_4151_);
return v_res_4156_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4163_; uint64_t v___x_4164_; 
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4163_);
return v___x_4164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4165_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4166_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4167_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set_uint64(v___x_4167_, sizeof(void*)*1, v___x_4165_);
return v___x_4167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4172_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
lean_ctor_set(v___x_4172_, 2, v___x_4171_);
lean_ctor_set(v___x_4172_, 3, v___x_4171_);
lean_ctor_set(v___x_4172_, 4, v___x_4171_);
lean_ctor_set(v___x_4172_, 5, v___x_4171_);
return v___x_4172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
lean_ctor_set(v___x_4174_, 2, v___x_4173_);
lean_ctor_set(v___x_4174_, 3, v___x_4173_);
lean_ctor_set(v___x_4174_, 4, v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v_declName_4177_, lean_object* v_stx_4178_, uint8_t v_attrKind_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_unsigned_to_nat(1u);
v___x_4184_ = l_Lean_Syntax_getArg(v_stx_4178_, v___x_4183_);
v___x_4185_ = l_Lean_getAttrParamOptPrio(v___x_4184_, v___y_4180_, v___y_4181_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; uint8_t v___x_4187_; uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; size_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref(v___x_4185_);
v___x_4187_ = 0;
v___x_4188_ = 1;
v___x_4189_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4190_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4191_ = lean_unsigned_to_nat(32u);
v___x_4192_ = lean_mk_empty_array_with_capacity(v___x_4191_);
v___x_4193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_4194_ = ((size_t)5ULL);
lean_inc_n(v___x_4175_, 6);
v___x_4195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4192_);
lean_ctor_set(v___x_4195_, 2, v___x_4175_);
lean_ctor_set(v___x_4195_, 3, v___x_4175_);
lean_ctor_set_usize(v___x_4195_, 4, v___x_4194_);
v___x_4196_ = lean_box(1);
lean_inc_ref(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4190_);
lean_ctor_set(v___x_4197_, 1, v___x_4195_);
lean_ctor_set(v___x_4197_, 2, v___x_4196_);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4175_);
v___x_4199_ = lean_box(0);
lean_inc(v___x_4176_);
v___x_4200_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4200_, 0, v___x_4189_);
lean_ctor_set(v___x_4200_, 1, v___x_4176_);
lean_ctor_set(v___x_4200_, 2, v___x_4197_);
lean_ctor_set(v___x_4200_, 3, v___x_4198_);
lean_ctor_set(v___x_4200_, 4, v___x_4199_);
lean_ctor_set(v___x_4200_, 5, v___x_4175_);
lean_ctor_set(v___x_4200_, 6, v___x_4199_);
lean_ctor_set_uint8(v___x_4200_, sizeof(void*)*7, v___x_4187_);
lean_ctor_set_uint8(v___x_4200_, sizeof(void*)*7 + 1, v___x_4187_);
lean_ctor_set_uint8(v___x_4200_, sizeof(void*)*7 + 2, v___x_4187_);
lean_ctor_set_uint8(v___x_4200_, sizeof(void*)*7 + 3, v___x_4188_);
v___x_4201_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4175_);
lean_ctor_set(v___x_4201_, 1, v___x_4175_);
lean_ctor_set(v___x_4201_, 2, v___x_4175_);
lean_ctor_set(v___x_4201_, 3, v___x_4175_);
lean_ctor_set(v___x_4201_, 4, v___x_4190_);
lean_ctor_set(v___x_4201_, 5, v___x_4190_);
lean_ctor_set(v___x_4201_, 6, v___x_4190_);
lean_ctor_set(v___x_4201_, 7, v___x_4190_);
lean_ctor_set(v___x_4201_, 8, v___x_4190_);
lean_ctor_set(v___x_4201_, 9, v___x_4190_);
v___x_4202_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4203_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4201_);
lean_ctor_set(v___x_4204_, 1, v___x_4202_);
lean_ctor_set(v___x_4204_, 2, v___x_4176_);
lean_ctor_set(v___x_4204_, 3, v___x_4195_);
lean_ctor_set(v___x_4204_, 4, v___x_4203_);
v___x_4205_ = lean_st_mk_ref(v___x_4204_);
v___x_4206_ = l_Lean_Meta_addInstance(v_declName_4177_, v_attrKind_4179_, v_a_4186_, v___x_4200_, v___x_4205_, v___y_4180_, v___y_4181_);
lean_dec_ref(v___x_4200_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4215_; 
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4215_ == 0)
{
lean_object* v_unused_4216_; 
v_unused_4216_ = lean_ctor_get(v___x_4206_, 0);
lean_dec(v_unused_4216_);
v___x_4208_ = v___x_4206_;
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v___x_4206_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4210_ = lean_st_ref_get(v___x_4205_);
lean_dec(v___x_4205_);
lean_dec(v___x_4210_);
v___x_4211_ = lean_box(0);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4211_);
v___x_4213_ = v___x_4208_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
else
{
lean_dec(v___x_4205_);
return v___x_4206_;
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_declName_4177_);
lean_dec(v___x_4176_);
lean_dec(v___x_4175_);
v_a_4217_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4185_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4185_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v_declName_4227_, lean_object* v_stx_4228_, lean_object* v_attrKind_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
uint8_t v_attrKind_boxed_4233_; lean_object* v_res_4234_; 
v_attrKind_boxed_4233_ = lean_unbox(v_attrKind_4229_);
v_res_4234_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4225_, v___x_4226_, v_declName_4227_, v_stx_4228_, v_attrKind_boxed_4233_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v_stx_4228_);
return v_res_4234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___f_4236_; 
v___x_4235_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4236_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4236_, 0, v___x_4235_);
return v___f_4236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___f_4303_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4304_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4305_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___f_4304_);
lean_ctor_set(v___x_4306_, 2, v___f_4303_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4309_ = l_Lean_registerBuiltinAttribute(v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4312_, lean_object* v_x_4313_, lean_object* v_x_4314_){
_start:
{
uint8_t v___x_4315_; 
v___x_4315_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4313_, v_x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4316_, lean_object* v_x_4317_, lean_object* v_x_4318_){
_start:
{
uint8_t v_res_4319_; lean_object* v_r_4320_; 
v_res_4319_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4316_, v_x_4317_, v_x_4318_);
lean_dec(v_x_4318_);
lean_dec_ref(v_x_4317_);
v_r_4320_ = lean_box(v_res_4319_);
return v_r_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4321_, lean_object* v_msg_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4322_, v___y_4323_, v___y_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_4327_, lean_object* v_msg_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4327_, v_msg_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
return v_res_4332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4333_, lean_object* v_x_4334_, size_t v_x_4335_, lean_object* v_x_4336_){
_start:
{
uint8_t v___x_4337_; 
v___x_4337_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4334_, v_x_4335_, v_x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4338_, lean_object* v_x_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_){
_start:
{
size_t v_x_3005__boxed_4342_; uint8_t v_res_4343_; lean_object* v_r_4344_; 
v_x_3005__boxed_4342_ = lean_unbox_usize(v_x_4340_);
lean_dec(v_x_4340_);
v_res_4343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_4338_, v_x_4339_, v_x_3005__boxed_4342_, v_x_4341_);
lean_dec(v_x_4341_);
lean_dec_ref(v_x_4339_);
v_r_4344_ = lean_box(v_res_4343_);
return v_r_4344_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4345_, lean_object* v_keys_4346_, lean_object* v_vals_4347_, lean_object* v_heq_4348_, lean_object* v_i_4349_, lean_object* v_k_4350_){
_start:
{
uint8_t v___x_4351_; 
v___x_4351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4346_, v_i_4349_, v_k_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4352_, lean_object* v_keys_4353_, lean_object* v_vals_4354_, lean_object* v_heq_4355_, lean_object* v_i_4356_, lean_object* v_k_4357_){
_start:
{
uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_res_4358_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4352_, v_keys_4353_, v_vals_4354_, v_heq_4355_, v_i_4356_, v_k_4357_);
lean_dec(v_k_4357_);
lean_dec_ref(v_vals_4354_);
lean_dec_ref(v_keys_4353_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4364_ = l_Lean_addBuiltinDocString(v___x_4362_, v___x_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; lean_object* v_env_4370_; lean_object* v___x_4371_; lean_object* v_ext_4372_; lean_object* v_toEnvExtension_4373_; lean_object* v_asyncMode_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_discrTree_4377_; lean_object* v___x_4378_; 
v___x_4369_ = lean_st_ref_get(v_a_4367_);
v_env_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc_ref(v_env_4370_);
lean_dec(v___x_4369_);
v___x_4371_ = l_Lean_Meta_instanceExtension;
v_ext_4372_ = lean_ctor_get(v___x_4371_, 1);
v_toEnvExtension_4373_ = lean_ctor_get(v_ext_4372_, 0);
v_asyncMode_4374_ = lean_ctor_get(v_toEnvExtension_4373_, 2);
v___x_4375_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4376_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4375_, v___x_4371_, v_env_4370_, v_asyncMode_4374_);
v_discrTree_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc_ref(v_discrTree_4377_);
lean_dec(v___x_4376_);
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v_discrTree_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4379_);
lean_dec(v_a_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_4383_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_4386_, v_a_4387_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4392_; lean_object* v_env_4393_; lean_object* v___x_4394_; lean_object* v_ext_4395_; lean_object* v_toEnvExtension_4396_; lean_object* v_asyncMode_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v_erased_4400_; lean_object* v___x_4401_; 
v___x_4392_ = lean_st_ref_get(v_a_4390_);
v_env_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc_ref(v_env_4393_);
lean_dec(v___x_4392_);
v___x_4394_ = l_Lean_Meta_instanceExtension;
v_ext_4395_ = lean_ctor_get(v___x_4394_, 1);
v_toEnvExtension_4396_ = lean_ctor_get(v_ext_4395_, 0);
v_asyncMode_4397_ = lean_ctor_get(v_toEnvExtension_4396_, 2);
v___x_4398_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4399_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4398_, v___x_4394_, v_env_4393_, v_asyncMode_4397_);
v_erased_4400_ = lean_ctor_get(v___x_4399_, 2);
lean_inc_ref(v_erased_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v_erased_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4402_);
lean_dec(v_a_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_Meta_getErasedInstances___redArg(v_a_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_Meta_getErasedInstances(v_a_4409_, v_a_4410_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
return v_res_4412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_4413_, lean_object* v_declName_4414_){
_start:
{
lean_object* v___x_4415_; lean_object* v_ext_4416_; lean_object* v_toEnvExtension_4417_; lean_object* v_asyncMode_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_instanceNames_4421_; uint8_t v___x_4422_; 
v___x_4415_ = l_Lean_Meta_instanceExtension;
v_ext_4416_ = lean_ctor_get(v___x_4415_, 1);
v_toEnvExtension_4417_ = lean_ctor_get(v_ext_4416_, 0);
v_asyncMode_4418_ = lean_ctor_get(v_toEnvExtension_4417_, 2);
v___x_4419_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4420_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4419_, v___x_4415_, v_env_4413_, v_asyncMode_4418_);
v_instanceNames_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc_ref(v_instanceNames_4421_);
lean_dec(v___x_4420_);
v___x_4422_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4421_, v_declName_4414_);
lean_dec_ref(v_instanceNames_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_4423_, lean_object* v_declName_4424_){
_start:
{
uint8_t v_res_4425_; lean_object* v_r_4426_; 
v_res_4425_ = l_Lean_Meta_isInstanceCore(v_env_4423_, v_declName_4424_);
lean_dec(v_declName_4424_);
v_r_4426_ = lean_box(v_res_4425_);
return v_r_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v___x_4430_; lean_object* v_env_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4430_ = lean_st_ref_get(v_a_4428_);
v_env_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc_ref(v_env_4431_);
lean_dec(v___x_4430_);
v___x_4432_ = l_Lean_Meta_isInstanceCore(v_env_4431_, v_declName_4427_);
v___x_4433_ = lean_box(v___x_4432_);
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_Meta_isInstance___redArg(v_declName_4435_, v_a_4436_);
lean_dec(v_a_4436_);
lean_dec(v_declName_4435_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_Meta_isInstance___redArg(v_declName_4439_, v_a_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Meta_isInstance(v_declName_4444_, v_a_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_declName_4444_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4449_, lean_object* v_vals_4450_, lean_object* v_i_4451_, lean_object* v_k_4452_){
_start:
{
lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4453_ = lean_array_get_size(v_keys_4449_);
v___x_4454_ = lean_nat_dec_lt(v_i_4451_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
lean_dec(v_i_4451_);
v___x_4455_ = lean_box(0);
return v___x_4455_;
}
else
{
lean_object* v_k_x27_4456_; uint8_t v___x_4457_; 
v_k_x27_4456_ = lean_array_fget_borrowed(v_keys_4449_, v_i_4451_);
v___x_4457_ = lean_name_eq(v_k_4452_, v_k_x27_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_unsigned_to_nat(1u);
v___x_4459_ = lean_nat_add(v_i_4451_, v___x_4458_);
lean_dec(v_i_4451_);
v_i_4451_ = v___x_4459_;
goto _start;
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = lean_array_fget_borrowed(v_vals_4450_, v_i_4451_);
lean_dec(v_i_4451_);
lean_inc(v___x_4461_);
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4463_, lean_object* v_vals_4464_, lean_object* v_i_4465_, lean_object* v_k_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4463_, v_vals_4464_, v_i_4465_, v_k_4466_);
lean_dec(v_k_4466_);
lean_dec_ref(v_vals_4464_);
lean_dec_ref(v_keys_4463_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_4468_, size_t v_x_4469_, lean_object* v_x_4470_){
_start:
{
if (lean_obj_tag(v_x_4468_) == 0)
{
lean_object* v_es_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4492_; 
v_es_4471_ = lean_ctor_get(v_x_4468_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_x_4468_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4473_ = v_x_4468_;
v_isShared_4474_ = v_isSharedCheck_4492_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_es_4471_);
lean_dec(v_x_4468_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4492_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4475_; size_t v___x_4476_; size_t v___x_4477_; size_t v___x_4478_; lean_object* v_j_4479_; lean_object* v___x_4480_; 
v___x_4475_ = lean_box(2);
v___x_4476_ = ((size_t)5ULL);
v___x_4477_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5___redArg___closed__1);
v___x_4478_ = lean_usize_land(v_x_4469_, v___x_4477_);
v_j_4479_ = lean_usize_to_nat(v___x_4478_);
v___x_4480_ = lean_array_get(v___x_4475_, v_es_4471_, v_j_4479_);
lean_dec(v_j_4479_);
lean_dec_ref(v_es_4471_);
switch(lean_obj_tag(v___x_4480_))
{
case 0:
{
lean_object* v_key_4481_; lean_object* v_val_4482_; uint8_t v___x_4483_; 
v_key_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_key_4481_);
v_val_4482_ = lean_ctor_get(v___x_4480_, 1);
lean_inc(v_val_4482_);
lean_dec_ref(v___x_4480_);
v___x_4483_ = lean_name_eq(v_x_4470_, v_key_4481_);
lean_dec(v_key_4481_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
lean_dec(v_val_4482_);
lean_del_object(v___x_4473_);
v___x_4484_ = lean_box(0);
return v___x_4484_;
}
else
{
lean_object* v___x_4486_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 1);
lean_ctor_set(v___x_4473_, 0, v_val_4482_);
v___x_4486_ = v___x_4473_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_val_4482_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
case 1:
{
lean_object* v_node_4488_; size_t v___x_4489_; 
lean_del_object(v___x_4473_);
v_node_4488_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_node_4488_);
lean_dec_ref(v___x_4480_);
v___x_4489_ = lean_usize_shift_right(v_x_4469_, v___x_4476_);
v_x_4468_ = v_node_4488_;
v_x_4469_ = v___x_4489_;
goto _start;
}
default: 
{
lean_object* v___x_4491_; 
lean_del_object(v___x_4473_);
v___x_4491_ = lean_box(0);
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_ks_4493_; lean_object* v_vs_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v_ks_4493_ = lean_ctor_get(v_x_4468_, 0);
lean_inc_ref(v_ks_4493_);
v_vs_4494_ = lean_ctor_get(v_x_4468_, 1);
lean_inc_ref(v_vs_4494_);
lean_dec_ref(v_x_4468_);
v___x_4495_ = lean_unsigned_to_nat(0u);
v___x_4496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4493_, v_vs_4494_, v___x_4495_, v_x_4470_);
lean_dec_ref(v_vs_4494_);
lean_dec_ref(v_ks_4493_);
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4497_, lean_object* v_x_4498_, lean_object* v_x_4499_){
_start:
{
size_t v_x_489__boxed_4500_; lean_object* v_res_4501_; 
v_x_489__boxed_4500_ = lean_unbox_usize(v_x_4498_);
lean_dec(v_x_4498_);
v_res_4501_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4497_, v_x_489__boxed_4500_, v_x_4499_);
lean_dec(v_x_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_4502_, lean_object* v_x_4503_){
_start:
{
uint64_t v___y_4505_; 
if (lean_obj_tag(v_x_4503_) == 0)
{
uint64_t v___x_4508_; 
v___x_4508_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__5_spec__11___redArg___closed__0);
v___y_4505_ = v___x_4508_;
goto v___jp_4504_;
}
else
{
uint64_t v_hash_4509_; 
v_hash_4509_ = lean_ctor_get_uint64(v_x_4503_, sizeof(void*)*2);
v___y_4505_ = v_hash_4509_;
goto v___jp_4504_;
}
v___jp_4504_:
{
size_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_uint64_to_usize(v___y_4505_);
v___x_4507_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4502_, v___x_4506_, v_x_4503_);
return v___x_4507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_4510_, lean_object* v_x_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4510_, v_x_4511_);
lean_dec(v_x_4511_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v_env_4517_; lean_object* v___x_4518_; lean_object* v_ext_4519_; lean_object* v_toEnvExtension_4520_; lean_object* v_asyncMode_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v_instanceNames_4524_; lean_object* v___x_4525_; 
v___x_4516_ = lean_st_ref_get(v_a_4514_);
v_env_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc_ref(v_env_4517_);
lean_dec(v___x_4516_);
v___x_4518_ = l_Lean_Meta_instanceExtension;
v_ext_4519_ = lean_ctor_get(v___x_4518_, 1);
v_toEnvExtension_4520_ = lean_ctor_get(v_ext_4519_, 0);
v_asyncMode_4521_ = lean_ctor_get(v_toEnvExtension_4520_, 2);
v___x_4522_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4523_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4522_, v___x_4518_, v_env_4517_, v_asyncMode_4521_);
v_instanceNames_4524_ = lean_ctor_get(v___x_4523_, 1);
lean_inc_ref(v_instanceNames_4524_);
lean_dec(v___x_4523_);
v___x_4525_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4524_, v_declName_4513_);
if (lean_obj_tag(v___x_4525_) == 1)
{
lean_object* v_val_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4535_; 
v_val_4526_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4528_ = v___x_4525_;
v_isShared_4529_ = v_isSharedCheck_4535_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_val_4526_);
lean_dec(v___x_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4535_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_priority_4530_; lean_object* v___x_4532_; 
v_priority_4530_ = lean_ctor_get(v_val_4526_, 2);
lean_inc(v_priority_4530_);
lean_dec(v_val_4526_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v_priority_4530_);
v___x_4532_ = v___x_4528_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_priority_4530_);
v___x_4532_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4533_; 
v___x_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
return v___x_4533_;
}
}
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec(v___x_4525_);
v___x_4536_ = lean_box(0);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec(v_declName_4538_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_4542_, v_a_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_declName_4547_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_4552_, lean_object* v_x_4553_, lean_object* v_x_4554_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_4553_, v_x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_4556_, lean_object* v_x_4557_, lean_object* v_x_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_4556_, v_x_4557_, v_x_4558_);
lean_dec(v_x_4558_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4560_, lean_object* v_x_4561_, size_t v_x_4562_, lean_object* v_x_4563_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_4561_, v_x_4562_, v_x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4565_, lean_object* v_x_4566_, lean_object* v_x_4567_, lean_object* v_x_4568_){
_start:
{
size_t v_x_617__boxed_4569_; lean_object* v_res_4570_; 
v_x_617__boxed_4569_ = lean_unbox_usize(v_x_4567_);
lean_dec(v_x_4567_);
v_res_4570_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_4565_, v_x_4566_, v_x_617__boxed_4569_, v_x_4568_);
lean_dec(v_x_4568_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4571_, lean_object* v_keys_4572_, lean_object* v_vals_4573_, lean_object* v_heq_4574_, lean_object* v_i_4575_, lean_object* v_k_4576_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4572_, v_vals_4573_, v_i_4575_, v_k_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4578_, lean_object* v_keys_4579_, lean_object* v_vals_4580_, lean_object* v_heq_4581_, lean_object* v_i_4582_, lean_object* v_k_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4578_, v_keys_4579_, v_vals_4580_, v_heq_4581_, v_i_4582_, v_k_4583_);
lean_dec(v_k_4583_);
lean_dec_ref(v_vals_4580_);
lean_dec_ref(v_keys_4579_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v_env_4589_; lean_object* v___x_4590_; lean_object* v_ext_4591_; lean_object* v_toEnvExtension_4592_; lean_object* v_asyncMode_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v_instanceNames_4596_; lean_object* v___x_4597_; 
v___x_4588_ = lean_st_ref_get(v_a_4586_);
v_env_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc_ref(v_env_4589_);
lean_dec(v___x_4588_);
v___x_4590_ = l_Lean_Meta_instanceExtension;
v_ext_4591_ = lean_ctor_get(v___x_4590_, 1);
v_toEnvExtension_4592_ = lean_ctor_get(v_ext_4591_, 0);
v_asyncMode_4593_ = lean_ctor_get(v_toEnvExtension_4592_, 2);
v___x_4594_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_4595_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4594_, v___x_4590_, v_env_4589_, v_asyncMode_4593_);
v_instanceNames_4596_ = lean_ctor_get(v___x_4595_, 1);
lean_inc_ref(v_instanceNames_4596_);
lean_dec(v___x_4595_);
v___x_4597_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_4596_, v_declName_4585_);
if (lean_obj_tag(v___x_4597_) == 1)
{
lean_object* v_val_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4608_; 
v_val_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4608_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_val_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4608_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
uint8_t v_attrKind_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v_attrKind_4602_ = lean_ctor_get_uint8(v_val_4598_, sizeof(void*)*5);
lean_dec(v_val_4598_);
v___x_4603_ = lean_box(v_attrKind_4602_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4603_);
v___x_4605_ = v___x_4600_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
}
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
lean_dec(v___x_4597_);
v___x_4609_ = lean_box(0);
v___x_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
return v___x_4610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4611_, v_a_4612_);
lean_dec(v_a_4612_);
lean_dec(v_declName_4611_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_4615_, v_a_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_4620_, v_a_4621_, v_a_4622_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_declName_4620_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_4629_, lean_object* v_v_4630_, lean_object* v_t_4631_){
_start:
{
if (lean_obj_tag(v_t_4631_) == 0)
{
lean_object* v_size_4632_; lean_object* v_k_4633_; lean_object* v_v_4634_; lean_object* v_l_4635_; lean_object* v_r_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4917_; 
v_size_4632_ = lean_ctor_get(v_t_4631_, 0);
v_k_4633_ = lean_ctor_get(v_t_4631_, 1);
v_v_4634_ = lean_ctor_get(v_t_4631_, 2);
v_l_4635_ = lean_ctor_get(v_t_4631_, 3);
v_r_4636_ = lean_ctor_get(v_t_4631_, 4);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_t_4631_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4638_ = v_t_4631_;
v_isShared_4639_ = v_isSharedCheck_4917_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_r_4636_);
lean_inc(v_l_4635_);
lean_inc(v_v_4634_);
lean_inc(v_k_4633_);
lean_inc(v_size_4632_);
lean_dec(v_t_4631_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4917_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
uint8_t v___x_4640_; 
v___x_4640_ = lean_nat_dec_lt(v_k_4633_, v_k_4629_);
if (v___x_4640_ == 0)
{
uint8_t v___x_4641_; 
v___x_4641_ = lean_nat_dec_eq(v_k_4633_, v_k_4629_);
if (v___x_4641_ == 0)
{
lean_object* v_impl_4642_; lean_object* v___x_4643_; 
lean_dec(v_size_4632_);
v_impl_4642_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4629_, v_v_4630_, v_r_4636_);
v___x_4643_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4635_) == 0)
{
lean_object* v_size_4644_; lean_object* v_size_4645_; lean_object* v_k_4646_; lean_object* v_v_4647_; lean_object* v_l_4648_; lean_object* v_r_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; uint8_t v___x_4652_; 
v_size_4644_ = lean_ctor_get(v_l_4635_, 0);
v_size_4645_ = lean_ctor_get(v_impl_4642_, 0);
lean_inc(v_size_4645_);
v_k_4646_ = lean_ctor_get(v_impl_4642_, 1);
lean_inc(v_k_4646_);
v_v_4647_ = lean_ctor_get(v_impl_4642_, 2);
lean_inc(v_v_4647_);
v_l_4648_ = lean_ctor_get(v_impl_4642_, 3);
lean_inc(v_l_4648_);
v_r_4649_ = lean_ctor_get(v_impl_4642_, 4);
lean_inc(v_r_4649_);
v___x_4650_ = lean_unsigned_to_nat(3u);
v___x_4651_ = lean_nat_mul(v___x_4650_, v_size_4644_);
v___x_4652_ = lean_nat_dec_lt(v___x_4651_, v_size_4645_);
lean_dec(v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
lean_dec(v_r_4649_);
lean_dec(v_l_4648_);
lean_dec(v_v_4647_);
lean_dec(v_k_4646_);
v___x_4653_ = lean_nat_add(v___x_4643_, v_size_4644_);
v___x_4654_ = lean_nat_add(v___x_4653_, v_size_4645_);
lean_dec(v_size_4645_);
lean_dec(v___x_4653_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_impl_4642_);
lean_ctor_set(v___x_4638_, 0, v___x_4654_);
v___x_4656_ = v___x_4638_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4657_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4657_, 3, v_l_4635_);
lean_ctor_set(v_reuseFailAlloc_4657_, 4, v_impl_4642_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
else
{
lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4721_; 
v_isSharedCheck_4721_ = !lean_is_exclusive(v_impl_4642_);
if (v_isSharedCheck_4721_ == 0)
{
lean_object* v_unused_4722_; lean_object* v_unused_4723_; lean_object* v_unused_4724_; lean_object* v_unused_4725_; lean_object* v_unused_4726_; 
v_unused_4722_ = lean_ctor_get(v_impl_4642_, 4);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_impl_4642_, 3);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_impl_4642_, 2);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_impl_4642_, 1);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_impl_4642_, 0);
lean_dec(v_unused_4726_);
v___x_4659_ = v_impl_4642_;
v_isShared_4660_ = v_isSharedCheck_4721_;
goto v_resetjp_4658_;
}
else
{
lean_dec(v_impl_4642_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4721_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v_size_4661_; lean_object* v_k_4662_; lean_object* v_v_4663_; lean_object* v_l_4664_; lean_object* v_r_4665_; lean_object* v_size_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v_size_4661_ = lean_ctor_get(v_l_4648_, 0);
v_k_4662_ = lean_ctor_get(v_l_4648_, 1);
v_v_4663_ = lean_ctor_get(v_l_4648_, 2);
v_l_4664_ = lean_ctor_get(v_l_4648_, 3);
v_r_4665_ = lean_ctor_get(v_l_4648_, 4);
v_size_4666_ = lean_ctor_get(v_r_4649_, 0);
v___x_4667_ = lean_unsigned_to_nat(2u);
v___x_4668_ = lean_nat_mul(v___x_4667_, v_size_4666_);
v___x_4669_ = lean_nat_dec_lt(v_size_4661_, v___x_4668_);
lean_dec(v___x_4668_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4697_; 
lean_inc(v_r_4665_);
lean_inc(v_l_4664_);
lean_inc(v_v_4663_);
lean_inc(v_k_4662_);
v_isSharedCheck_4697_ = !lean_is_exclusive(v_l_4648_);
if (v_isSharedCheck_4697_ == 0)
{
lean_object* v_unused_4698_; lean_object* v_unused_4699_; lean_object* v_unused_4700_; lean_object* v_unused_4701_; lean_object* v_unused_4702_; 
v_unused_4698_ = lean_ctor_get(v_l_4648_, 4);
lean_dec(v_unused_4698_);
v_unused_4699_ = lean_ctor_get(v_l_4648_, 3);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_l_4648_, 2);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_l_4648_, 1);
lean_dec(v_unused_4701_);
v_unused_4702_ = lean_ctor_get(v_l_4648_, 0);
lean_dec(v_unused_4702_);
v___x_4671_ = v_l_4648_;
v_isShared_4672_ = v_isSharedCheck_4697_;
goto v_resetjp_4670_;
}
else
{
lean_dec(v_l_4648_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4697_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4687_; 
v___x_4673_ = lean_nat_add(v___x_4643_, v_size_4644_);
v___x_4674_ = lean_nat_add(v___x_4673_, v_size_4645_);
lean_dec(v_size_4645_);
if (lean_obj_tag(v_l_4664_) == 0)
{
lean_object* v_size_4695_; 
v_size_4695_ = lean_ctor_get(v_l_4664_, 0);
lean_inc(v_size_4695_);
v___y_4687_ = v_size_4695_;
goto v___jp_4686_;
}
else
{
lean_object* v___x_4696_; 
v___x_4696_ = lean_unsigned_to_nat(0u);
v___y_4687_ = v___x_4696_;
goto v___jp_4686_;
}
v___jp_4675_:
{
lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4679_ = lean_nat_add(v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec(v___y_4677_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 4, v_r_4649_);
lean_ctor_set(v___x_4671_, 3, v_r_4665_);
lean_ctor_set(v___x_4671_, 2, v_v_4647_);
lean_ctor_set(v___x_4671_, 1, v_k_4646_);
lean_ctor_set(v___x_4671_, 0, v___x_4679_);
v___x_4681_ = v___x_4671_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_k_4646_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_v_4647_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v_r_4665_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_r_4649_);
v___x_4681_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4683_; 
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 4, v___x_4681_);
lean_ctor_set(v___x_4659_, 3, v___y_4676_);
lean_ctor_set(v___x_4659_, 2, v_v_4663_);
lean_ctor_set(v___x_4659_, 1, v_k_4662_);
lean_ctor_set(v___x_4659_, 0, v___x_4674_);
v___x_4683_ = v___x_4659_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v_k_4662_);
lean_ctor_set(v_reuseFailAlloc_4684_, 2, v_v_4663_);
lean_ctor_set(v_reuseFailAlloc_4684_, 3, v___y_4676_);
lean_ctor_set(v_reuseFailAlloc_4684_, 4, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
v___jp_4686_:
{
lean_object* v___x_4688_; lean_object* v___x_4690_; 
v___x_4688_ = lean_nat_add(v___x_4673_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec(v___x_4673_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_l_4664_);
lean_ctor_set(v___x_4638_, 0, v___x_4688_);
v___x_4690_ = v___x_4638_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v_l_4635_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v_l_4664_);
v___x_4690_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4691_; 
v___x_4691_ = lean_nat_add(v___x_4643_, v_size_4666_);
if (lean_obj_tag(v_r_4665_) == 0)
{
lean_object* v_size_4692_; 
v_size_4692_ = lean_ctor_get(v_r_4665_, 0);
lean_inc(v_size_4692_);
v___y_4676_ = v___x_4690_;
v___y_4677_ = v___x_4691_;
v___y_4678_ = v_size_4692_;
goto v___jp_4675_;
}
else
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_unsigned_to_nat(0u);
v___y_4676_ = v___x_4690_;
v___y_4677_ = v___x_4691_;
v___y_4678_ = v___x_4693_;
goto v___jp_4675_;
}
}
}
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4707_; 
lean_del_object(v___x_4638_);
v___x_4703_ = lean_nat_add(v___x_4643_, v_size_4644_);
v___x_4704_ = lean_nat_add(v___x_4703_, v_size_4645_);
lean_dec(v_size_4645_);
v___x_4705_ = lean_nat_add(v___x_4703_, v_size_4661_);
lean_dec(v___x_4703_);
lean_inc_ref(v_l_4635_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 4, v_l_4648_);
lean_ctor_set(v___x_4659_, 3, v_l_4635_);
lean_ctor_set(v___x_4659_, 2, v_v_4634_);
lean_ctor_set(v___x_4659_, 1, v_k_4633_);
lean_ctor_set(v___x_4659_, 0, v___x_4705_);
v___x_4707_ = v___x_4659_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4720_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4720_, 3, v_l_4635_);
lean_ctor_set(v_reuseFailAlloc_4720_, 4, v_l_4648_);
v___x_4707_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
v_isSharedCheck_4714_ = !lean_is_exclusive(v_l_4635_);
if (v_isSharedCheck_4714_ == 0)
{
lean_object* v_unused_4715_; lean_object* v_unused_4716_; lean_object* v_unused_4717_; lean_object* v_unused_4718_; lean_object* v_unused_4719_; 
v_unused_4715_ = lean_ctor_get(v_l_4635_, 4);
lean_dec(v_unused_4715_);
v_unused_4716_ = lean_ctor_get(v_l_4635_, 3);
lean_dec(v_unused_4716_);
v_unused_4717_ = lean_ctor_get(v_l_4635_, 2);
lean_dec(v_unused_4717_);
v_unused_4718_ = lean_ctor_get(v_l_4635_, 1);
lean_dec(v_unused_4718_);
v_unused_4719_ = lean_ctor_get(v_l_4635_, 0);
lean_dec(v_unused_4719_);
v___x_4709_ = v_l_4635_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_dec(v_l_4635_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 4, v_r_4649_);
lean_ctor_set(v___x_4709_, 3, v___x_4707_);
lean_ctor_set(v___x_4709_, 2, v_v_4647_);
lean_ctor_set(v___x_4709_, 1, v_k_4646_);
lean_ctor_set(v___x_4709_, 0, v___x_4704_);
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4704_);
lean_ctor_set(v_reuseFailAlloc_4713_, 1, v_k_4646_);
lean_ctor_set(v_reuseFailAlloc_4713_, 2, v_v_4647_);
lean_ctor_set(v_reuseFailAlloc_4713_, 3, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4713_, 4, v_r_4649_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4727_; 
v_l_4727_ = lean_ctor_get(v_impl_4642_, 3);
lean_inc(v_l_4727_);
if (lean_obj_tag(v_l_4727_) == 0)
{
lean_object* v_r_4728_; lean_object* v_k_4729_; lean_object* v_v_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4753_; 
v_r_4728_ = lean_ctor_get(v_impl_4642_, 4);
v_k_4729_ = lean_ctor_get(v_impl_4642_, 1);
v_v_4730_ = lean_ctor_get(v_impl_4642_, 2);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_impl_4642_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; lean_object* v_unused_4755_; 
v_unused_4754_ = lean_ctor_get(v_impl_4642_, 3);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_impl_4642_, 0);
lean_dec(v_unused_4755_);
v___x_4732_ = v_impl_4642_;
v_isShared_4733_ = v_isSharedCheck_4753_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_r_4728_);
lean_inc(v_v_4730_);
lean_inc(v_k_4729_);
lean_dec(v_impl_4642_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4753_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v_k_4734_; lean_object* v_v_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4749_; 
v_k_4734_ = lean_ctor_get(v_l_4727_, 1);
v_v_4735_ = lean_ctor_get(v_l_4727_, 2);
v_isSharedCheck_4749_ = !lean_is_exclusive(v_l_4727_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; 
v_unused_4750_ = lean_ctor_get(v_l_4727_, 4);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_l_4727_, 3);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_l_4727_, 0);
lean_dec(v_unused_4752_);
v___x_4737_ = v_l_4727_;
v_isShared_4738_ = v_isSharedCheck_4749_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_v_4735_);
lean_inc(v_k_4734_);
lean_dec(v_l_4727_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4749_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4739_; lean_object* v___x_4741_; 
v___x_4739_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4728_, 2);
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 4, v_r_4728_);
lean_ctor_set(v___x_4737_, 3, v_r_4728_);
lean_ctor_set(v___x_4737_, 2, v_v_4634_);
lean_ctor_set(v___x_4737_, 1, v_k_4633_);
lean_ctor_set(v___x_4737_, 0, v___x_4643_);
v___x_4741_ = v___x_4737_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_r_4728_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v_r_4728_);
v___x_4741_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4743_; 
lean_inc(v_r_4728_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 3, v_r_4728_);
lean_ctor_set(v___x_4732_, 0, v___x_4643_);
v___x_4743_ = v___x_4732_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_k_4729_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_v_4730_);
lean_ctor_set(v_reuseFailAlloc_4747_, 3, v_r_4728_);
lean_ctor_set(v_reuseFailAlloc_4747_, 4, v_r_4728_);
v___x_4743_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4745_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v___x_4743_);
lean_ctor_set(v___x_4638_, 3, v___x_4741_);
lean_ctor_set(v___x_4638_, 2, v_v_4735_);
lean_ctor_set(v___x_4638_, 1, v_k_4734_);
lean_ctor_set(v___x_4638_, 0, v___x_4739_);
v___x_4745_ = v___x_4638_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4739_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_k_4734_);
lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_v_4735_);
lean_ctor_set(v_reuseFailAlloc_4746_, 3, v___x_4741_);
lean_ctor_set(v_reuseFailAlloc_4746_, 4, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
}
else
{
lean_object* v_r_4756_; 
v_r_4756_ = lean_ctor_get(v_impl_4642_, 4);
lean_inc(v_r_4756_);
if (lean_obj_tag(v_r_4756_) == 0)
{
lean_object* v_k_4757_; lean_object* v_v_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4769_; 
v_k_4757_ = lean_ctor_get(v_impl_4642_, 1);
v_v_4758_ = lean_ctor_get(v_impl_4642_, 2);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_impl_4642_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; lean_object* v_unused_4771_; lean_object* v_unused_4772_; 
v_unused_4770_ = lean_ctor_get(v_impl_4642_, 4);
lean_dec(v_unused_4770_);
v_unused_4771_ = lean_ctor_get(v_impl_4642_, 3);
lean_dec(v_unused_4771_);
v_unused_4772_ = lean_ctor_get(v_impl_4642_, 0);
lean_dec(v_unused_4772_);
v___x_4760_ = v_impl_4642_;
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_v_4758_);
lean_inc(v_k_4757_);
lean_dec(v_impl_4642_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4762_ = lean_unsigned_to_nat(3u);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 4, v_l_4727_);
lean_ctor_set(v___x_4760_, 2, v_v_4634_);
lean_ctor_set(v___x_4760_, 1, v_k_4633_);
lean_ctor_set(v___x_4760_, 0, v___x_4643_);
v___x_4764_ = v___x_4760_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4768_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4768_, 3, v_l_4727_);
lean_ctor_set(v_reuseFailAlloc_4768_, 4, v_l_4727_);
v___x_4764_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4766_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_r_4756_);
lean_ctor_set(v___x_4638_, 3, v___x_4764_);
lean_ctor_set(v___x_4638_, 2, v_v_4758_);
lean_ctor_set(v___x_4638_, 1, v_k_4757_);
lean_ctor_set(v___x_4638_, 0, v___x_4762_);
v___x_4766_ = v___x_4638_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4762_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_k_4757_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_v_4758_);
lean_ctor_set(v_reuseFailAlloc_4767_, 3, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4767_, 4, v_r_4756_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4775_; 
v___x_4773_ = lean_unsigned_to_nat(2u);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_impl_4642_);
lean_ctor_set(v___x_4638_, 3, v_r_4756_);
lean_ctor_set(v___x_4638_, 0, v___x_4773_);
v___x_4775_ = v___x_4638_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4773_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4776_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4776_, 3, v_r_4756_);
lean_ctor_set(v_reuseFailAlloc_4776_, 4, v_impl_4642_);
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
}
else
{
lean_object* v___x_4778_; 
lean_dec(v_v_4634_);
lean_dec(v_k_4633_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 2, v_v_4630_);
lean_ctor_set(v___x_4638_, 1, v_k_4629_);
v___x_4778_ = v___x_4638_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_size_4632_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_k_4629_);
lean_ctor_set(v_reuseFailAlloc_4779_, 2, v_v_4630_);
lean_ctor_set(v_reuseFailAlloc_4779_, 3, v_l_4635_);
lean_ctor_set(v_reuseFailAlloc_4779_, 4, v_r_4636_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
else
{
lean_object* v_impl_4780_; lean_object* v___x_4781_; 
lean_dec(v_size_4632_);
v_impl_4780_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4629_, v_v_4630_, v_l_4635_);
v___x_4781_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4636_) == 0)
{
lean_object* v_size_4782_; lean_object* v_size_4783_; lean_object* v_k_4784_; lean_object* v_v_4785_; lean_object* v_l_4786_; lean_object* v_r_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_size_4782_ = lean_ctor_get(v_r_4636_, 0);
v_size_4783_ = lean_ctor_get(v_impl_4780_, 0);
lean_inc(v_size_4783_);
v_k_4784_ = lean_ctor_get(v_impl_4780_, 1);
lean_inc(v_k_4784_);
v_v_4785_ = lean_ctor_get(v_impl_4780_, 2);
lean_inc(v_v_4785_);
v_l_4786_ = lean_ctor_get(v_impl_4780_, 3);
lean_inc(v_l_4786_);
v_r_4787_ = lean_ctor_get(v_impl_4780_, 4);
lean_inc(v_r_4787_);
v___x_4788_ = lean_unsigned_to_nat(3u);
v___x_4789_ = lean_nat_mul(v___x_4788_, v_size_4782_);
v___x_4790_ = lean_nat_dec_lt(v___x_4789_, v_size_4783_);
lean_dec(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4794_; 
lean_dec(v_r_4787_);
lean_dec(v_l_4786_);
lean_dec(v_v_4785_);
lean_dec(v_k_4784_);
v___x_4791_ = lean_nat_add(v___x_4781_, v_size_4783_);
lean_dec(v_size_4783_);
v___x_4792_ = lean_nat_add(v___x_4791_, v_size_4782_);
lean_dec(v___x_4791_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 3, v_impl_4780_);
lean_ctor_set(v___x_4638_, 0, v___x_4792_);
v___x_4794_ = v___x_4638_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4795_, 3, v_impl_4780_);
lean_ctor_set(v_reuseFailAlloc_4795_, 4, v_r_4636_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
else
{
lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4861_; 
v_isSharedCheck_4861_ = !lean_is_exclusive(v_impl_4780_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; lean_object* v_unused_4863_; lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; 
v_unused_4862_ = lean_ctor_get(v_impl_4780_, 4);
lean_dec(v_unused_4862_);
v_unused_4863_ = lean_ctor_get(v_impl_4780_, 3);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_impl_4780_, 2);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_impl_4780_, 1);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_impl_4780_, 0);
lean_dec(v_unused_4866_);
v___x_4797_ = v_impl_4780_;
v_isShared_4798_ = v_isSharedCheck_4861_;
goto v_resetjp_4796_;
}
else
{
lean_dec(v_impl_4780_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4861_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v_size_4799_; lean_object* v_size_4800_; lean_object* v_k_4801_; lean_object* v_v_4802_; lean_object* v_l_4803_; lean_object* v_r_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; 
v_size_4799_ = lean_ctor_get(v_l_4786_, 0);
v_size_4800_ = lean_ctor_get(v_r_4787_, 0);
v_k_4801_ = lean_ctor_get(v_r_4787_, 1);
v_v_4802_ = lean_ctor_get(v_r_4787_, 2);
v_l_4803_ = lean_ctor_get(v_r_4787_, 3);
v_r_4804_ = lean_ctor_get(v_r_4787_, 4);
v___x_4805_ = lean_unsigned_to_nat(2u);
v___x_4806_ = lean_nat_mul(v___x_4805_, v_size_4799_);
v___x_4807_ = lean_nat_dec_lt(v_size_4800_, v___x_4806_);
lean_dec(v___x_4806_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4836_; 
lean_inc(v_r_4804_);
lean_inc(v_l_4803_);
lean_inc(v_v_4802_);
lean_inc(v_k_4801_);
v_isSharedCheck_4836_ = !lean_is_exclusive(v_r_4787_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; lean_object* v_unused_4838_; lean_object* v_unused_4839_; lean_object* v_unused_4840_; lean_object* v_unused_4841_; 
v_unused_4837_ = lean_ctor_get(v_r_4787_, 4);
lean_dec(v_unused_4837_);
v_unused_4838_ = lean_ctor_get(v_r_4787_, 3);
lean_dec(v_unused_4838_);
v_unused_4839_ = lean_ctor_get(v_r_4787_, 2);
lean_dec(v_unused_4839_);
v_unused_4840_ = lean_ctor_get(v_r_4787_, 1);
lean_dec(v_unused_4840_);
v_unused_4841_ = lean_ctor_get(v_r_4787_, 0);
lean_dec(v_unused_4841_);
v___x_4809_ = v_r_4787_;
v_isShared_4810_ = v_isSharedCheck_4836_;
goto v_resetjp_4808_;
}
else
{
lean_dec(v_r_4787_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4836_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___x_4824_; lean_object* v___y_4826_; 
v___x_4811_ = lean_nat_add(v___x_4781_, v_size_4783_);
lean_dec(v_size_4783_);
v___x_4812_ = lean_nat_add(v___x_4811_, v_size_4782_);
lean_dec(v___x_4811_);
v___x_4824_ = lean_nat_add(v___x_4781_, v_size_4799_);
if (lean_obj_tag(v_l_4803_) == 0)
{
lean_object* v_size_4834_; 
v_size_4834_ = lean_ctor_get(v_l_4803_, 0);
lean_inc(v_size_4834_);
v___y_4826_ = v_size_4834_;
goto v___jp_4825_;
}
else
{
lean_object* v___x_4835_; 
v___x_4835_ = lean_unsigned_to_nat(0u);
v___y_4826_ = v___x_4835_;
goto v___jp_4825_;
}
v___jp_4813_:
{
lean_object* v___x_4817_; lean_object* v___x_4819_; 
v___x_4817_ = lean_nat_add(v___y_4815_, v___y_4816_);
lean_dec(v___y_4816_);
lean_dec(v___y_4815_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 4, v_r_4636_);
lean_ctor_set(v___x_4809_, 3, v_r_4804_);
lean_ctor_set(v___x_4809_, 2, v_v_4634_);
lean_ctor_set(v___x_4809_, 1, v_k_4633_);
lean_ctor_set(v___x_4809_, 0, v___x_4817_);
v___x_4819_ = v___x_4809_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4823_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4823_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4823_, 3, v_r_4804_);
lean_ctor_set(v_reuseFailAlloc_4823_, 4, v_r_4636_);
v___x_4819_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
lean_object* v___x_4821_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 4, v___x_4819_);
lean_ctor_set(v___x_4797_, 3, v___y_4814_);
lean_ctor_set(v___x_4797_, 2, v_v_4802_);
lean_ctor_set(v___x_4797_, 1, v_k_4801_);
lean_ctor_set(v___x_4797_, 0, v___x_4812_);
v___x_4821_ = v___x_4797_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_k_4801_);
lean_ctor_set(v_reuseFailAlloc_4822_, 2, v_v_4802_);
lean_ctor_set(v_reuseFailAlloc_4822_, 3, v___y_4814_);
lean_ctor_set(v_reuseFailAlloc_4822_, 4, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
v___jp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_nat_add(v___x_4824_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec(v___x_4824_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_l_4803_);
lean_ctor_set(v___x_4638_, 3, v_l_4786_);
lean_ctor_set(v___x_4638_, 2, v_v_4785_);
lean_ctor_set(v___x_4638_, 1, v_k_4784_);
lean_ctor_set(v___x_4638_, 0, v___x_4827_);
v___x_4829_ = v___x_4638_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_k_4784_);
lean_ctor_set(v_reuseFailAlloc_4833_, 2, v_v_4785_);
lean_ctor_set(v_reuseFailAlloc_4833_, 3, v_l_4786_);
lean_ctor_set(v_reuseFailAlloc_4833_, 4, v_l_4803_);
v___x_4829_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_nat_add(v___x_4781_, v_size_4782_);
if (lean_obj_tag(v_r_4804_) == 0)
{
lean_object* v_size_4831_; 
v_size_4831_ = lean_ctor_get(v_r_4804_, 0);
lean_inc(v_size_4831_);
v___y_4814_ = v___x_4829_;
v___y_4815_ = v___x_4830_;
v___y_4816_ = v_size_4831_;
goto v___jp_4813_;
}
else
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_unsigned_to_nat(0u);
v___y_4814_ = v___x_4829_;
v___y_4815_ = v___x_4830_;
v___y_4816_ = v___x_4832_;
goto v___jp_4813_;
}
}
}
}
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
lean_del_object(v___x_4638_);
v___x_4842_ = lean_nat_add(v___x_4781_, v_size_4783_);
lean_dec(v_size_4783_);
v___x_4843_ = lean_nat_add(v___x_4842_, v_size_4782_);
lean_dec(v___x_4842_);
v___x_4844_ = lean_nat_add(v___x_4781_, v_size_4782_);
v___x_4845_ = lean_nat_add(v___x_4844_, v_size_4800_);
lean_dec(v___x_4844_);
lean_inc_ref(v_r_4636_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 4, v_r_4636_);
lean_ctor_set(v___x_4797_, 3, v_r_4787_);
lean_ctor_set(v___x_4797_, 2, v_v_4634_);
lean_ctor_set(v___x_4797_, 1, v_k_4633_);
lean_ctor_set(v___x_4797_, 0, v___x_4845_);
v___x_4847_ = v___x_4797_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_r_4787_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_r_4636_);
v___x_4847_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_isSharedCheck_4854_ = !lean_is_exclusive(v_r_4636_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; lean_object* v_unused_4856_; lean_object* v_unused_4857_; lean_object* v_unused_4858_; lean_object* v_unused_4859_; 
v_unused_4855_ = lean_ctor_get(v_r_4636_, 4);
lean_dec(v_unused_4855_);
v_unused_4856_ = lean_ctor_get(v_r_4636_, 3);
lean_dec(v_unused_4856_);
v_unused_4857_ = lean_ctor_get(v_r_4636_, 2);
lean_dec(v_unused_4857_);
v_unused_4858_ = lean_ctor_get(v_r_4636_, 1);
lean_dec(v_unused_4858_);
v_unused_4859_ = lean_ctor_get(v_r_4636_, 0);
lean_dec(v_unused_4859_);
v___x_4849_ = v_r_4636_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_dec(v_r_4636_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 4, v___x_4847_);
lean_ctor_set(v___x_4849_, 3, v_l_4786_);
lean_ctor_set(v___x_4849_, 2, v_v_4785_);
lean_ctor_set(v___x_4849_, 1, v_k_4784_);
lean_ctor_set(v___x_4849_, 0, v___x_4843_);
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4853_, 1, v_k_4784_);
lean_ctor_set(v_reuseFailAlloc_4853_, 2, v_v_4785_);
lean_ctor_set(v_reuseFailAlloc_4853_, 3, v_l_4786_);
lean_ctor_set(v_reuseFailAlloc_4853_, 4, v___x_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4867_; 
v_l_4867_ = lean_ctor_get(v_impl_4780_, 3);
lean_inc(v_l_4867_);
if (lean_obj_tag(v_l_4867_) == 0)
{
lean_object* v_r_4868_; lean_object* v_k_4869_; lean_object* v_v_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4881_; 
v_r_4868_ = lean_ctor_get(v_impl_4780_, 4);
v_k_4869_ = lean_ctor_get(v_impl_4780_, 1);
v_v_4870_ = lean_ctor_get(v_impl_4780_, 2);
v_isSharedCheck_4881_ = !lean_is_exclusive(v_impl_4780_);
if (v_isSharedCheck_4881_ == 0)
{
lean_object* v_unused_4882_; lean_object* v_unused_4883_; 
v_unused_4882_ = lean_ctor_get(v_impl_4780_, 3);
lean_dec(v_unused_4882_);
v_unused_4883_ = lean_ctor_get(v_impl_4780_, 0);
lean_dec(v_unused_4883_);
v___x_4872_ = v_impl_4780_;
v_isShared_4873_ = v_isSharedCheck_4881_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_r_4868_);
lean_inc(v_v_4870_);
lean_inc(v_k_4869_);
lean_dec(v_impl_4780_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4881_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4874_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4868_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 3, v_r_4868_);
lean_ctor_set(v___x_4872_, 2, v_v_4634_);
lean_ctor_set(v___x_4872_, 1, v_k_4633_);
lean_ctor_set(v___x_4872_, 0, v___x_4781_);
v___x_4876_ = v___x_4872_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4880_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4880_, 3, v_r_4868_);
lean_ctor_set(v_reuseFailAlloc_4880_, 4, v_r_4868_);
v___x_4876_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4878_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v___x_4876_);
lean_ctor_set(v___x_4638_, 3, v_l_4867_);
lean_ctor_set(v___x_4638_, 2, v_v_4870_);
lean_ctor_set(v___x_4638_, 1, v_k_4869_);
lean_ctor_set(v___x_4638_, 0, v___x_4874_);
v___x_4878_ = v___x_4638_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v_k_4869_);
lean_ctor_set(v_reuseFailAlloc_4879_, 2, v_v_4870_);
lean_ctor_set(v_reuseFailAlloc_4879_, 3, v_l_4867_);
lean_ctor_set(v_reuseFailAlloc_4879_, 4, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
else
{
lean_object* v_r_4884_; 
v_r_4884_ = lean_ctor_get(v_impl_4780_, 4);
lean_inc(v_r_4884_);
if (lean_obj_tag(v_r_4884_) == 0)
{
lean_object* v_k_4885_; lean_object* v_v_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4909_; 
v_k_4885_ = lean_ctor_get(v_impl_4780_, 1);
v_v_4886_ = lean_ctor_get(v_impl_4780_, 2);
v_isSharedCheck_4909_ = !lean_is_exclusive(v_impl_4780_);
if (v_isSharedCheck_4909_ == 0)
{
lean_object* v_unused_4910_; lean_object* v_unused_4911_; lean_object* v_unused_4912_; 
v_unused_4910_ = lean_ctor_get(v_impl_4780_, 4);
lean_dec(v_unused_4910_);
v_unused_4911_ = lean_ctor_get(v_impl_4780_, 3);
lean_dec(v_unused_4911_);
v_unused_4912_ = lean_ctor_get(v_impl_4780_, 0);
lean_dec(v_unused_4912_);
v___x_4888_ = v_impl_4780_;
v_isShared_4889_ = v_isSharedCheck_4909_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_v_4886_);
lean_inc(v_k_4885_);
lean_dec(v_impl_4780_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4909_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v_k_4890_; lean_object* v_v_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4905_; 
v_k_4890_ = lean_ctor_get(v_r_4884_, 1);
v_v_4891_ = lean_ctor_get(v_r_4884_, 2);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_r_4884_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; lean_object* v_unused_4907_; lean_object* v_unused_4908_; 
v_unused_4906_ = lean_ctor_get(v_r_4884_, 4);
lean_dec(v_unused_4906_);
v_unused_4907_ = lean_ctor_get(v_r_4884_, 3);
lean_dec(v_unused_4907_);
v_unused_4908_ = lean_ctor_get(v_r_4884_, 0);
lean_dec(v_unused_4908_);
v___x_4893_ = v_r_4884_;
v_isShared_4894_ = v_isSharedCheck_4905_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_v_4891_);
lean_inc(v_k_4890_);
lean_dec(v_r_4884_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4905_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4895_; lean_object* v___x_4897_; 
v___x_4895_ = lean_unsigned_to_nat(3u);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 4, v_l_4867_);
lean_ctor_set(v___x_4893_, 3, v_l_4867_);
lean_ctor_set(v___x_4893_, 2, v_v_4886_);
lean_ctor_set(v___x_4893_, 1, v_k_4885_);
lean_ctor_set(v___x_4893_, 0, v___x_4781_);
v___x_4897_ = v___x_4893_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_k_4885_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_v_4886_);
lean_ctor_set(v_reuseFailAlloc_4904_, 3, v_l_4867_);
lean_ctor_set(v_reuseFailAlloc_4904_, 4, v_l_4867_);
v___x_4897_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
lean_object* v___x_4899_; 
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 4, v_l_4867_);
lean_ctor_set(v___x_4888_, 2, v_v_4634_);
lean_ctor_set(v___x_4888_, 1, v_k_4633_);
lean_ctor_set(v___x_4888_, 0, v___x_4781_);
v___x_4899_ = v___x_4888_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4903_, 3, v_l_4867_);
lean_ctor_set(v_reuseFailAlloc_4903_, 4, v_l_4867_);
v___x_4899_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4901_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v___x_4899_);
lean_ctor_set(v___x_4638_, 3, v___x_4897_);
lean_ctor_set(v___x_4638_, 2, v_v_4891_);
lean_ctor_set(v___x_4638_, 1, v_k_4890_);
lean_ctor_set(v___x_4638_, 0, v___x_4895_);
v___x_4901_ = v___x_4638_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4895_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_k_4890_);
lean_ctor_set(v_reuseFailAlloc_4902_, 2, v_v_4891_);
lean_ctor_set(v_reuseFailAlloc_4902_, 3, v___x_4897_);
lean_ctor_set(v_reuseFailAlloc_4902_, 4, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4913_ = lean_unsigned_to_nat(2u);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v_r_4884_);
lean_ctor_set(v___x_4638_, 3, v_impl_4780_);
lean_ctor_set(v___x_4638_, 0, v___x_4913_);
v___x_4915_ = v___x_4638_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_k_4633_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_v_4634_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v_impl_4780_);
lean_ctor_set(v_reuseFailAlloc_4916_, 4, v_r_4884_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = lean_unsigned_to_nat(1u);
v___x_4919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v_k_4629_);
lean_ctor_set(v___x_4919_, 2, v_v_4630_);
lean_ctor_set(v___x_4919_, 3, v_t_4631_);
lean_ctor_set(v___x_4919_, 4, v_t_4631_);
return v___x_4919_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_4920_, lean_object* v_t_4921_){
_start:
{
if (lean_obj_tag(v_t_4921_) == 0)
{
lean_object* v_k_4922_; lean_object* v_l_4923_; lean_object* v_r_4924_; uint8_t v___x_4925_; 
v_k_4922_ = lean_ctor_get(v_t_4921_, 1);
v_l_4923_ = lean_ctor_get(v_t_4921_, 3);
v_r_4924_ = lean_ctor_get(v_t_4921_, 4);
v___x_4925_ = lean_nat_dec_lt(v_k_4922_, v_k_4920_);
if (v___x_4925_ == 0)
{
uint8_t v___x_4926_; 
v___x_4926_ = lean_nat_dec_eq(v_k_4922_, v_k_4920_);
if (v___x_4926_ == 0)
{
v_t_4921_ = v_r_4924_;
goto _start;
}
else
{
return v___x_4926_;
}
}
else
{
v_t_4921_ = v_l_4923_;
goto _start;
}
}
else
{
uint8_t v___x_4929_; 
v___x_4929_ = 0;
return v___x_4929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_4930_, lean_object* v_t_4931_){
_start:
{
uint8_t v_res_4932_; lean_object* v_r_4933_; 
v_res_4932_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4930_, v_t_4931_);
lean_dec(v_t_4931_);
lean_dec(v_k_4930_);
v_r_4933_ = lean_box(v_res_4932_);
return v_r_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_4934_, lean_object* v_e_4935_){
_start:
{
lean_object* v_defaultInstances_4936_; lean_object* v_priorities_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4964_; 
v_defaultInstances_4936_ = lean_ctor_get(v_d_4934_, 0);
v_priorities_4937_ = lean_ctor_get(v_d_4934_, 1);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_d_4934_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4939_ = v_d_4934_;
v_isShared_4940_ = v_isSharedCheck_4964_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_priorities_4937_);
lean_inc(v_defaultInstances_4936_);
lean_dec(v_d_4934_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4964_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_className_4941_; lean_object* v_instanceName_4942_; lean_object* v_priority_4943_; lean_object* v___y_4945_; uint8_t v___x_4961_; 
v_className_4941_ = lean_ctor_get(v_e_4935_, 0);
lean_inc(v_className_4941_);
v_instanceName_4942_ = lean_ctor_get(v_e_4935_, 1);
lean_inc(v_instanceName_4942_);
v_priority_4943_ = lean_ctor_get(v_e_4935_, 2);
lean_inc(v_priority_4943_);
lean_dec_ref(v_e_4935_);
v___x_4961_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_4943_, v_priorities_4937_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = lean_box(0);
lean_inc(v_priority_4943_);
v___x_4963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_4943_, v___x_4962_, v_priorities_4937_);
v___y_4945_ = v___x_4963_;
goto v___jp_4944_;
}
else
{
v___y_4945_ = v_priorities_4937_;
goto v___jp_4944_;
}
v___jp_4944_:
{
lean_object* v___x_4946_; 
v___x_4946_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_4936_, v_className_4941_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4952_; 
v___x_4947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4947_, 0, v_instanceName_4942_);
lean_ctor_set(v___x_4947_, 1, v_priority_4943_);
v___x_4948_ = lean_box(0);
v___x_4949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4941_, v___x_4949_, v_defaultInstances_4936_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___y_4945_);
lean_ctor_set(v___x_4939_, 0, v___x_4950_);
v___x_4952_ = v___x_4939_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4950_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v___y_4945_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
else
{
lean_object* v_val_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
v_val_4954_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_val_4954_);
lean_dec_ref(v___x_4946_);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v_instanceName_4942_);
lean_ctor_set(v___x_4955_, 1, v_priority_4943_);
v___x_4956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v_val_4954_);
v___x_4957_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_4941_, v___x_4956_, v_defaultInstances_4936_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___y_4945_);
lean_ctor_set(v___x_4939_, 0, v___x_4957_);
v___x_4959_ = v___x_4939_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4960_, 1, v___y_4945_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_4965_, lean_object* v_k_4966_, lean_object* v_t_4967_){
_start:
{
uint8_t v___x_4968_; 
v___x_4968_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_4966_, v_t_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_4969_, lean_object* v_k_4970_, lean_object* v_t_4971_){
_start:
{
uint8_t v_res_4972_; lean_object* v_r_4973_; 
v_res_4972_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_4969_, v_k_4970_, v_t_4971_);
lean_dec(v_t_4971_);
lean_dec(v_k_4970_);
v_r_4973_ = lean_box(v_res_4972_);
return v_r_4973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_4974_, lean_object* v_k_4975_, lean_object* v_v_4976_, lean_object* v_t_4977_, lean_object* v_hl_4978_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_4975_, v_v_4976_, v_t_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_4980_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_array_mk(v_es_4980_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4982_, size_t v_i_4983_, size_t v_stop_4984_, lean_object* v_b_4985_){
_start:
{
uint8_t v___x_4986_; 
v___x_4986_ = lean_usize_dec_eq(v_i_4983_, v_stop_4984_);
if (v___x_4986_ == 0)
{
lean_object* v___x_4987_; lean_object* v___x_4988_; size_t v___x_4989_; size_t v___x_4990_; 
v___x_4987_ = lean_array_uget_borrowed(v_as_4982_, v_i_4983_);
lean_inc(v___x_4987_);
v___x_4988_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_4985_, v___x_4987_);
v___x_4989_ = ((size_t)1ULL);
v___x_4990_ = lean_usize_add(v_i_4983_, v___x_4989_);
v_i_4983_ = v___x_4990_;
v_b_4985_ = v___x_4988_;
goto _start;
}
else
{
return v_b_4985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4992_, lean_object* v_i_4993_, lean_object* v_stop_4994_, lean_object* v_b_4995_){
_start:
{
size_t v_i_boxed_4996_; size_t v_stop_boxed_4997_; lean_object* v_res_4998_; 
v_i_boxed_4996_ = lean_unbox_usize(v_i_4993_);
lean_dec(v_i_4993_);
v_stop_boxed_4997_ = lean_unbox_usize(v_stop_4994_);
lean_dec(v_stop_4994_);
v_res_4998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v_as_4992_, v_i_boxed_4996_, v_stop_boxed_4997_, v_b_4995_);
lean_dec_ref(v_as_4992_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_4999_, size_t v_i_5000_, size_t v_stop_5001_, lean_object* v_b_5002_){
_start:
{
lean_object* v___y_5004_; uint8_t v___x_5008_; 
v___x_5008_ = lean_usize_dec_eq(v_i_5000_, v_stop_5001_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v___x_5009_ = lean_array_uget_borrowed(v_as_4999_, v_i_5000_);
v___x_5010_ = lean_unsigned_to_nat(0u);
v___x_5011_ = lean_array_get_size(v___x_5009_);
v___x_5012_ = lean_nat_dec_lt(v___x_5010_, v___x_5011_);
if (v___x_5012_ == 0)
{
v___y_5004_ = v_b_5002_;
goto v___jp_5003_;
}
else
{
uint8_t v___x_5013_; 
v___x_5013_ = lean_nat_dec_le(v___x_5011_, v___x_5011_);
if (v___x_5013_ == 0)
{
if (v___x_5012_ == 0)
{
v___y_5004_ = v_b_5002_;
goto v___jp_5003_;
}
else
{
size_t v___x_5014_; size_t v___x_5015_; lean_object* v___x_5016_; 
v___x_5014_ = ((size_t)0ULL);
v___x_5015_ = lean_usize_of_nat(v___x_5011_);
v___x_5016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5009_, v___x_5014_, v___x_5015_, v_b_5002_);
v___y_5004_ = v___x_5016_;
goto v___jp_5003_;
}
}
else
{
size_t v___x_5017_; size_t v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = ((size_t)0ULL);
v___x_5018_ = lean_usize_of_nat(v___x_5011_);
v___x_5019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__0(v___x_5009_, v___x_5017_, v___x_5018_, v_b_5002_);
v___y_5004_ = v___x_5019_;
goto v___jp_5003_;
}
}
}
else
{
return v_b_5002_;
}
v___jp_5003_:
{
size_t v___x_5005_; size_t v___x_5006_; 
v___x_5005_ = ((size_t)1ULL);
v___x_5006_ = lean_usize_add(v_i_5000_, v___x_5005_);
v_i_5000_ = v___x_5006_;
v_b_5002_ = v___y_5004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_5020_, lean_object* v_i_5021_, lean_object* v_stop_5022_, lean_object* v_b_5023_){
_start:
{
size_t v_i_boxed_5024_; size_t v_stop_boxed_5025_; lean_object* v_res_5026_; 
v_i_boxed_5024_ = lean_unbox_usize(v_i_5021_);
lean_dec(v_i_5021_);
v_stop_boxed_5025_ = lean_unbox_usize(v_stop_5022_);
lean_dec(v_stop_5022_);
v_res_5026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5020_, v_i_boxed_5024_, v_stop_boxed_5025_, v_b_5023_);
lean_dec_ref(v_as_5020_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(lean_object* v_initState_5027_, lean_object* v_as_5028_){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; uint8_t v___x_5031_; 
v___x_5029_ = lean_unsigned_to_nat(0u);
v___x_5030_ = lean_array_get_size(v_as_5028_);
v___x_5031_ = lean_nat_dec_lt(v___x_5029_, v___x_5030_);
if (v___x_5031_ == 0)
{
return v_initState_5027_;
}
else
{
uint8_t v___x_5032_; 
v___x_5032_ = lean_nat_dec_le(v___x_5030_, v___x_5030_);
if (v___x_5032_ == 0)
{
if (v___x_5031_ == 0)
{
return v_initState_5027_;
}
else
{
size_t v___x_5033_; size_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5033_ = ((size_t)0ULL);
v___x_5034_ = lean_usize_of_nat(v___x_5030_);
v___x_5035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5028_, v___x_5033_, v___x_5034_, v_initState_5027_);
return v___x_5035_;
}
}
else
{
size_t v___x_5036_; size_t v___x_5037_; lean_object* v___x_5038_; 
v___x_5036_ = ((size_t)0ULL);
v___x_5037_ = lean_usize_of_nat(v___x_5030_);
v___x_5038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0_spec__1(v_as_5028_, v___x_5036_, v___x_5037_, v_initState_5027_);
return v___x_5038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_5039_, lean_object* v_as_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v_initState_5039_, v_as_5040_);
lean_dec_ref(v_as_5040_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(lean_object* v_es_5042_){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5044_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2__spec__0(v___x_5043_, v_es_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_es_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(v_es_5045_);
lean_dec_ref(v_es_5045_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_));
v___x_5064_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2____boxed(lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1486461684____hygCtx___hyg_2_();
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v___x_5071_; lean_object* v_nextMacroScope_5072_; lean_object* v_ngen_5073_; lean_object* v_auxDeclNGen_5074_; lean_object* v_traceState_5075_; lean_object* v_messages_5076_; lean_object* v_infoState_5077_; lean_object* v_snapshotTasks_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5104_; 
v___x_5071_ = lean_st_ref_take(v___y_5069_);
v_nextMacroScope_5072_ = lean_ctor_get(v___x_5071_, 1);
v_ngen_5073_ = lean_ctor_get(v___x_5071_, 2);
v_auxDeclNGen_5074_ = lean_ctor_get(v___x_5071_, 3);
v_traceState_5075_ = lean_ctor_get(v___x_5071_, 4);
v_messages_5076_ = lean_ctor_get(v___x_5071_, 6);
v_infoState_5077_ = lean_ctor_get(v___x_5071_, 7);
v_snapshotTasks_5078_ = lean_ctor_get(v___x_5071_, 8);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; lean_object* v_unused_5106_; 
v_unused_5105_ = lean_ctor_get(v___x_5071_, 5);
lean_dec(v_unused_5105_);
v_unused_5106_ = lean_ctor_get(v___x_5071_, 0);
lean_dec(v_unused_5106_);
v___x_5080_ = v___x_5071_;
v_isShared_5081_ = v_isSharedCheck_5104_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_snapshotTasks_5078_);
lean_inc(v_infoState_5077_);
lean_inc(v_messages_5076_);
lean_inc(v_traceState_5075_);
lean_inc(v_auxDeclNGen_5074_);
lean_inc(v_ngen_5073_);
lean_inc(v_nextMacroScope_5072_);
lean_dec(v___x_5071_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5104_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5082_; lean_object* v___x_5084_; 
v___x_5082_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 5, v___x_5082_);
lean_ctor_set(v___x_5080_, 0, v_env_5067_);
v___x_5084_ = v___x_5080_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_env_5067_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_nextMacroScope_5072_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_ngen_5073_);
lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_auxDeclNGen_5074_);
lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_traceState_5075_);
lean_ctor_set(v_reuseFailAlloc_5103_, 5, v___x_5082_);
lean_ctor_set(v_reuseFailAlloc_5103_, 6, v_messages_5076_);
lean_ctor_set(v_reuseFailAlloc_5103_, 7, v_infoState_5077_);
lean_ctor_set(v_reuseFailAlloc_5103_, 8, v_snapshotTasks_5078_);
v___x_5084_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v_mctx_5087_; lean_object* v_zetaDeltaFVarIds_5088_; lean_object* v_postponed_5089_; lean_object* v_diag_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5101_; 
v___x_5085_ = lean_st_ref_set(v___y_5069_, v___x_5084_);
v___x_5086_ = lean_st_ref_take(v___y_5068_);
v_mctx_5087_ = lean_ctor_get(v___x_5086_, 0);
v_zetaDeltaFVarIds_5088_ = lean_ctor_get(v___x_5086_, 2);
v_postponed_5089_ = lean_ctor_get(v___x_5086_, 3);
v_diag_5090_ = lean_ctor_get(v___x_5086_, 4);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5101_ == 0)
{
lean_object* v_unused_5102_; 
v_unused_5102_ = lean_ctor_get(v___x_5086_, 1);
lean_dec(v_unused_5102_);
v___x_5092_ = v___x_5086_;
v_isShared_5093_ = v_isSharedCheck_5101_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_diag_5090_);
lean_inc(v_postponed_5089_);
lean_inc(v_zetaDeltaFVarIds_5088_);
lean_inc(v_mctx_5087_);
lean_dec(v___x_5086_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5101_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5094_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5094_);
v___x_5096_ = v___x_5092_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_mctx_5087_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5100_, 2, v_zetaDeltaFVarIds_5088_);
lean_ctor_set(v_reuseFailAlloc_5100_, 3, v_postponed_5089_);
lean_ctor_set(v_reuseFailAlloc_5100_, 4, v_diag_5090_);
v___x_5096_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5097_ = lean_st_ref_set(v___y_5068_, v___x_5096_);
v___x_5098_ = lean_box(0);
v___x_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5098_);
return v___x_5099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5107_, v___y_5108_, v___y_5109_);
lean_dec(v___y_5109_);
lean_dec(v___y_5108_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5112_, v___y_5114_, v___y_5116_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
return v_res_5125_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5128_ = l_Lean_stringToMessageData(v___x_5127_);
return v___x_5128_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5130_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5131_ = l_Lean_stringToMessageData(v___x_5130_);
return v___x_5131_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5133_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5134_ = l_Lean_stringToMessageData(v___x_5133_);
return v___x_5134_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5137_ = l_Lean_stringToMessageData(v___x_5136_);
return v___x_5137_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5140_ = l_Lean_stringToMessageData(v___x_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5141_, lean_object* v_prio_5142_, lean_object* v_x_5143_, lean_object* v_type_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Lean_Expr_getAppFn(v_type_5144_);
if (lean_obj_tag(v___x_5150_) == 4)
{
lean_object* v_declName_5151_; lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___x_5166_; lean_object* v_env_5167_; uint8_t v___x_5168_; 
v_declName_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc_n(v_declName_5151_, 2);
lean_dec_ref(v___x_5150_);
v___x_5166_ = lean_st_ref_get(v___y_5148_);
v_env_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc_ref(v_env_5167_);
lean_dec(v___x_5166_);
v___x_5168_ = lean_is_class(v_env_5167_, v_declName_5151_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_dec(v_prio_5142_);
v___x_5169_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5170_ = l_Lean_MessageData_ofConstName(v_declName_5141_, v___x_5168_);
v___x_5171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5169_);
lean_ctor_set(v___x_5171_, 1, v___x_5170_);
v___x_5172_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5171_);
lean_ctor_set(v___x_5173_, 1, v___x_5172_);
lean_inc(v_declName_5151_);
v___x_5174_ = l_Lean_MessageData_ofName(v_declName_5151_);
v___x_5175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5173_);
lean_ctor_set(v___x_5175_, 1, v___x_5174_);
v___x_5176_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5175_);
lean_ctor_set(v___x_5177_, 1, v___x_5176_);
v___x_5178_ = l_Lean_MessageData_ofConstName(v_declName_5151_, v___x_5168_);
v___x_5179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5177_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5179_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5181_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
return v___x_5182_;
}
else
{
v___y_5153_ = v___y_5145_;
v___y_5154_ = v___y_5146_;
v___y_5155_ = v___y_5147_;
v___y_5156_ = v___y_5148_;
goto v___jp_5152_;
}
v___jp_5152_:
{
lean_object* v___x_5157_; lean_object* v_env_5158_; lean_object* v___x_5159_; lean_object* v_toEnvExtension_5160_; lean_object* v_asyncMode_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5157_ = lean_st_ref_get(v___y_5156_);
v_env_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc_ref(v_env_5158_);
lean_dec(v___x_5157_);
v___x_5159_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5160_ = lean_ctor_get(v___x_5159_, 0);
v_asyncMode_5161_ = lean_ctor_get(v_toEnvExtension_5160_, 2);
v___x_5162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5162_, 0, v_declName_5151_);
lean_ctor_set(v___x_5162_, 1, v_declName_5141_);
lean_ctor_set(v___x_5162_, 2, v_prio_5142_);
v___x_5163_ = lean_box(0);
v___x_5164_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5159_, v_env_5158_, v___x_5162_, v_asyncMode_5161_, v___x_5163_);
v___x_5165_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5164_, v___y_5154_, v___y_5156_);
return v___x_5165_;
}
}
else
{
lean_object* v___x_5183_; uint8_t v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
lean_dec_ref(v___x_5150_);
lean_dec(v_prio_5142_);
v___x_5183_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5184_ = 0;
v___x_5185_ = l_Lean_MessageData_ofConstName(v_declName_5141_, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5183_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5186_);
lean_ctor_set(v___x_5188_, 1, v___x_5187_);
v___x_5189_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5188_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
return v___x_5189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5190_, lean_object* v_prio_5191_, lean_object* v_x_5192_, lean_object* v_type_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5190_, v_prio_5191_, v_x_5192_, v_type_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec_ref(v_type_5193_);
lean_dec_ref(v_x_5192_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5200_, lean_object* v_prio_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v___x_5207_; lean_object* v_env_5208_; uint8_t v___x_5209_; lean_object* v___x_5210_; 
v___x_5207_ = lean_st_ref_get(v_a_5205_);
v_env_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc_ref(v_env_5208_);
lean_dec(v___x_5207_);
v___x_5209_ = 0;
lean_inc(v_declName_5200_);
v___x_5210_ = l_Lean_Environment_find_x3f(v_env_5208_, v_declName_5200_, v___x_5209_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
lean_dec(v_prio_5201_);
v___x_5211_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5212_ = l_Lean_MessageData_ofConstName(v_declName_5200_, v___x_5209_);
v___x_5213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5211_);
lean_ctor_set(v___x_5213_, 1, v___x_5212_);
v___x_5214_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5213_);
lean_ctor_set(v___x_5215_, 1, v___x_5214_);
v___x_5216_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5215_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_);
return v___x_5216_;
}
else
{
lean_object* v_val_5217_; lean_object* v___f_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v_val_5217_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_val_5217_);
lean_dec_ref(v___x_5210_);
v___f_5218_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5218_, 0, v_declName_5200_);
lean_closure_set(v___f_5218_, 1, v_prio_5201_);
v___x_5219_ = l_Lean_ConstantInfo_type(v_val_5217_);
lean_dec(v_val_5217_);
v___x_5220_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5219_, v___f_5218_, v___x_5209_, v___x_5209_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_);
return v___x_5220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5221_, lean_object* v_prio_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Lean_Meta_addDefaultInstance(v_declName_5221_, v_prio_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
return v_res_5228_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5230_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5231_ = l_Lean_stringToMessageData(v___x_5230_);
return v___x_5231_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5233_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5234_ = l_Lean_stringToMessageData(v___x_5233_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5238_, uint8_t v_kind_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___y_5249_; 
v___x_5243_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5244_ = l_Lean_MessageData_ofName(v_name_5238_);
v___x_5245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5243_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5245_);
lean_ctor_set(v___x_5247_, 1, v___x_5246_);
switch(v_kind_5239_)
{
case 0:
{
lean_object* v___x_5256_; 
v___x_5256_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5249_ = v___x_5256_;
goto v___jp_5248_;
}
case 1:
{
lean_object* v___x_5257_; 
v___x_5257_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5249_ = v___x_5257_;
goto v___jp_5248_;
}
default: 
{
lean_object* v___x_5258_; 
v___x_5258_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5249_ = v___x_5258_;
goto v___jp_5248_;
}
}
v___jp_5248_:
{
lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
lean_inc_ref(v___y_5249_);
v___x_5250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5250_, 0, v___y_5249_);
v___x_5251_ = l_Lean_MessageData_ofFormat(v___x_5250_);
v___x_5252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5247_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5252_);
lean_ctor_set(v___x_5254_, 1, v___x_5253_);
v___x_5255_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5254_, v___y_5240_, v___y_5241_);
return v___x_5255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5259_, lean_object* v_kind_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
uint8_t v_kind_boxed_5264_; lean_object* v_res_5265_; 
v_kind_boxed_5264_ = lean_unbox(v_kind_5260_);
v_res_5265_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5259_, v_kind_boxed_5264_, v___y_5261_, v___y_5262_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5266_, lean_object* v___x_5267_, lean_object* v___x_5268_, lean_object* v_declName_5269_, lean_object* v_stx_5270_, uint8_t v_kind_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5275_ = lean_unsigned_to_nat(1u);
v___x_5276_ = l_Lean_Syntax_getArg(v_stx_5270_, v___x_5275_);
v___x_5277_ = l_Lean_getAttrParamOptPrio(v___x_5276_, v___y_5272_, v___y_5273_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___y_5280_; lean_object* v___y_5281_; uint8_t v___x_5312_; uint8_t v___x_5313_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc(v_a_5278_);
lean_dec_ref(v___x_5277_);
v___x_5312_ = 0;
v___x_5313_ = l_Lean_instBEqAttributeKind_beq(v_kind_5271_, v___x_5312_);
if (v___x_5313_ == 0)
{
lean_object* v___x_5314_; 
lean_dec(v_a_5278_);
lean_dec(v_declName_5269_);
lean_dec(v___x_5267_);
lean_dec(v___x_5266_);
v___x_5314_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5268_, v_kind_5271_, v___y_5272_, v___y_5273_);
return v___x_5314_;
}
else
{
lean_dec(v___x_5268_);
v___y_5280_ = v___y_5272_;
v___y_5281_ = v___y_5273_;
goto v___jp_5279_;
}
v___jp_5279_:
{
uint8_t v___x_5282_; uint8_t v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; size_t v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5282_ = 0;
v___x_5283_ = 1;
v___x_5284_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5285_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5286_ = lean_unsigned_to_nat(32u);
v___x_5287_ = lean_mk_empty_array_with_capacity(v___x_5286_);
v___x_5288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__9_spec__11_spec__13___redArg___closed__3);
v___x_5289_ = ((size_t)5ULL);
lean_inc_n(v___x_5266_, 6);
v___x_5290_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5290_, 0, v___x_5288_);
lean_ctor_set(v___x_5290_, 1, v___x_5287_);
lean_ctor_set(v___x_5290_, 2, v___x_5266_);
lean_ctor_set(v___x_5290_, 3, v___x_5266_);
lean_ctor_set_usize(v___x_5290_, 4, v___x_5289_);
v___x_5291_ = lean_box(1);
lean_inc_ref(v___x_5290_);
v___x_5292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5285_);
lean_ctor_set(v___x_5292_, 1, v___x_5290_);
lean_ctor_set(v___x_5292_, 2, v___x_5291_);
v___x_5293_ = lean_mk_empty_array_with_capacity(v___x_5266_);
v___x_5294_ = lean_box(0);
lean_inc(v___x_5267_);
v___x_5295_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5295_, 0, v___x_5284_);
lean_ctor_set(v___x_5295_, 1, v___x_5267_);
lean_ctor_set(v___x_5295_, 2, v___x_5292_);
lean_ctor_set(v___x_5295_, 3, v___x_5293_);
lean_ctor_set(v___x_5295_, 4, v___x_5294_);
lean_ctor_set(v___x_5295_, 5, v___x_5266_);
lean_ctor_set(v___x_5295_, 6, v___x_5294_);
lean_ctor_set_uint8(v___x_5295_, sizeof(void*)*7, v___x_5282_);
lean_ctor_set_uint8(v___x_5295_, sizeof(void*)*7 + 1, v___x_5282_);
lean_ctor_set_uint8(v___x_5295_, sizeof(void*)*7 + 2, v___x_5282_);
lean_ctor_set_uint8(v___x_5295_, sizeof(void*)*7 + 3, v___x_5283_);
v___x_5296_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5266_);
lean_ctor_set(v___x_5296_, 1, v___x_5266_);
lean_ctor_set(v___x_5296_, 2, v___x_5266_);
lean_ctor_set(v___x_5296_, 3, v___x_5266_);
lean_ctor_set(v___x_5296_, 4, v___x_5285_);
lean_ctor_set(v___x_5296_, 5, v___x_5285_);
lean_ctor_set(v___x_5296_, 6, v___x_5285_);
lean_ctor_set(v___x_5296_, 7, v___x_5285_);
lean_ctor_set(v___x_5296_, 8, v___x_5285_);
lean_ctor_set(v___x_5296_, 9, v___x_5285_);
v___x_5297_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5298_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5296_);
lean_ctor_set(v___x_5299_, 1, v___x_5297_);
lean_ctor_set(v___x_5299_, 2, v___x_5267_);
lean_ctor_set(v___x_5299_, 3, v___x_5290_);
lean_ctor_set(v___x_5299_, 4, v___x_5298_);
v___x_5300_ = lean_st_mk_ref(v___x_5299_);
v___x_5301_ = l_Lean_Meta_addDefaultInstance(v_declName_5269_, v_a_5278_, v___x_5295_, v___x_5300_, v___y_5280_, v___y_5281_);
lean_dec_ref(v___x_5295_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5310_; 
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5310_ == 0)
{
lean_object* v_unused_5311_; 
v_unused_5311_ = lean_ctor_get(v___x_5301_, 0);
lean_dec(v_unused_5311_);
v___x_5303_ = v___x_5301_;
v_isShared_5304_ = v_isSharedCheck_5310_;
goto v_resetjp_5302_;
}
else
{
lean_dec(v___x_5301_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5310_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5308_; 
v___x_5305_ = lean_st_ref_get(v___x_5300_);
lean_dec(v___x_5300_);
lean_dec(v___x_5305_);
v___x_5306_ = lean_box(0);
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 0, v___x_5306_);
v___x_5308_ = v___x_5303_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5306_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
else
{
lean_dec(v___x_5300_);
return v___x_5301_;
}
}
}
else
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5322_; 
lean_dec(v_declName_5269_);
lean_dec(v___x_5268_);
lean_dec(v___x_5267_);
lean_dec(v___x_5266_);
v_a_5315_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5317_ = v___x_5277_;
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5277_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5323_, lean_object* v___x_5324_, lean_object* v___x_5325_, lean_object* v_declName_5326_, lean_object* v_stx_5327_, lean_object* v_kind_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
uint8_t v_kind_boxed_5332_; lean_object* v_res_5333_; 
v_kind_boxed_5332_ = lean_unbox(v_kind_5328_);
v_res_5333_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5323_, v___x_5324_, v___x_5325_, v_declName_5326_, v_stx_5327_, v_kind_boxed_5332_, v___y_5329_, v___y_5330_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v_stx_5327_);
return v_res_5333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5335_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5336_ = l_Lean_stringToMessageData(v___x_5335_);
return v___x_5336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5339_ = l_Lean_stringToMessageData(v___x_5338_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5340_, lean_object* v_decl_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5345_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5346_ = l_Lean_MessageData_ofName(v___x_5340_);
v___x_5347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5345_);
lean_ctor_set(v___x_5347_, 1, v___x_5346_);
v___x_5348_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_5349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5349_, 0, v___x_5347_);
lean_ctor_set(v___x_5349_, 1, v___x_5348_);
v___x_5350_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5349_, v___y_5342_, v___y_5343_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_5351_, lean_object* v_decl_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_5351_, v_decl_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v_decl_5352_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5389_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5390_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_5391_ = l_Lean_registerBuiltinAttribute(v___x_5390_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v___x_5392_; uint8_t v___x_5393_; lean_object* v___x_5394_; 
lean_dec_ref(v___x_5391_);
v___x_5392_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_5393_ = 0;
v___x_5394_ = l_Lean_registerTraceClass(v___x_5392_, v___x_5393_, v___x_5389_);
return v___x_5394_;
}
else
{
return v___x_5391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_5397_, lean_object* v_name_5398_, uint8_t v_kind_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5398_, v_kind_5399_, v___y_5400_, v___y_5401_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_5404_, lean_object* v_name_5405_, lean_object* v_kind_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
uint8_t v_kind_boxed_5410_; lean_object* v_res_5411_; 
v_kind_boxed_5410_ = lean_unbox(v_kind_5406_);
v_res_5411_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_5404_, v_name_5405_, v_kind_boxed_5410_, v___y_5407_, v___y_5408_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_5412_, lean_object* v_toPure_5413_, lean_object* v_____do__lift_5414_){
_start:
{
lean_object* v___x_5415_; lean_object* v_toEnvExtension_5416_; lean_object* v_asyncMode_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v_priorities_5420_; lean_object* v___x_5421_; 
v___x_5415_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5416_ = lean_ctor_get(v___x_5415_, 0);
v_asyncMode_5417_ = lean_ctor_get(v_toEnvExtension_5416_, 2);
v___x_5418_ = lean_box(0);
v___x_5419_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5412_, v___x_5415_, v_____do__lift_5414_, v_asyncMode_5417_, v___x_5418_);
v_priorities_5420_ = lean_ctor_get(v___x_5419_, 1);
lean_inc(v_priorities_5420_);
lean_dec(v___x_5419_);
v___x_5421_ = lean_apply_2(v_toPure_5413_, lean_box(0), v_priorities_5420_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_5422_, lean_object* v_inst_5423_){
_start:
{
lean_object* v_toApplicative_5424_; lean_object* v_toBind_5425_; lean_object* v_getEnv_5426_; lean_object* v_toPure_5427_; lean_object* v___x_5428_; lean_object* v___f_5429_; lean_object* v___x_5430_; 
v_toApplicative_5424_ = lean_ctor_get(v_inst_5422_, 0);
lean_inc_ref(v_toApplicative_5424_);
v_toBind_5425_ = lean_ctor_get(v_inst_5422_, 1);
lean_inc(v_toBind_5425_);
lean_dec_ref(v_inst_5422_);
v_getEnv_5426_ = lean_ctor_get(v_inst_5423_, 0);
lean_inc(v_getEnv_5426_);
lean_dec_ref(v_inst_5423_);
v_toPure_5427_ = lean_ctor_get(v_toApplicative_5424_, 1);
lean_inc(v_toPure_5427_);
lean_dec_ref(v_toApplicative_5424_);
v___x_5428_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5429_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5429_, 0, v___x_5428_);
lean_closure_set(v___f_5429_, 1, v_toPure_5427_);
v___x_5430_ = lean_apply_4(v_toBind_5425_, lean_box(0), lean_box(0), v_getEnv_5426_, v___f_5429_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_5431_, lean_object* v_inst_5432_, lean_object* v_inst_5433_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_5432_, v_inst_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v___x_5435_, lean_object* v_className_5436_, lean_object* v_toPure_5437_, lean_object* v_____do__lift_5438_){
_start:
{
lean_object* v___x_5439_; lean_object* v_toEnvExtension_5440_; lean_object* v_asyncMode_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v_defaultInstances_5444_; lean_object* v___x_5445_; 
v___x_5439_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5440_ = lean_ctor_get(v___x_5439_, 0);
v_asyncMode_5441_ = lean_ctor_get(v_toEnvExtension_5440_, 2);
v___x_5442_ = lean_box(0);
v___x_5443_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5435_, v___x_5439_, v_____do__lift_5438_, v_asyncMode_5441_, v___x_5442_);
v_defaultInstances_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v_defaultInstances_5444_);
lean_dec(v___x_5443_);
v___x_5445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5444_, v_className_5436_);
lean_dec(v_defaultInstances_5444_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = lean_box(0);
v___x_5447_ = lean_apply_2(v_toPure_5437_, lean_box(0), v___x_5446_);
return v___x_5447_;
}
else
{
lean_object* v_val_5448_; lean_object* v___x_5449_; 
v_val_5448_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_val_5448_);
lean_dec_ref(v___x_5445_);
v___x_5449_ = lean_apply_2(v_toPure_5437_, lean_box(0), v_val_5448_);
return v___x_5449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v___x_5450_, lean_object* v_className_5451_, lean_object* v_toPure_5452_, lean_object* v_____do__lift_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v___x_5450_, v_className_5451_, v_toPure_5452_, v_____do__lift_5453_);
lean_dec(v_className_5451_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_5455_, lean_object* v_inst_5456_, lean_object* v_className_5457_){
_start:
{
lean_object* v_toApplicative_5458_; lean_object* v_toBind_5459_; lean_object* v_getEnv_5460_; lean_object* v_toPure_5461_; lean_object* v___x_5462_; lean_object* v___f_5463_; lean_object* v___x_5464_; 
v_toApplicative_5458_ = lean_ctor_get(v_inst_5455_, 0);
lean_inc_ref(v_toApplicative_5458_);
v_toBind_5459_ = lean_ctor_get(v_inst_5455_, 1);
lean_inc(v_toBind_5459_);
lean_dec_ref(v_inst_5455_);
v_getEnv_5460_ = lean_ctor_get(v_inst_5456_, 0);
lean_inc(v_getEnv_5460_);
lean_dec_ref(v_inst_5456_);
v_toPure_5461_ = lean_ctor_get(v_toApplicative_5458_, 1);
lean_inc(v_toPure_5461_);
lean_dec_ref(v_toApplicative_5458_);
v___x_5462_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_5463_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5463_, 0, v___x_5462_);
lean_closure_set(v___f_5463_, 1, v_className_5457_);
lean_closure_set(v___f_5463_, 2, v_toPure_5461_);
v___x_5464_ = lean_apply_4(v_toBind_5459_, lean_box(0), lean_box(0), v_getEnv_5460_, v___f_5463_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_5465_, lean_object* v_inst_5466_, lean_object* v_inst_5467_, lean_object* v_className_5468_){
_start:
{
lean_object* v___x_5469_; 
v___x_5469_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_5466_, v_inst_5467_, v_className_5468_);
return v___x_5469_;
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
