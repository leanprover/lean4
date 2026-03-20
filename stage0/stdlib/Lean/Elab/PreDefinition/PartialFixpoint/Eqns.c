// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: public import Lean.Elab.PreDefinition.FixedParams import Init.Internal.Order.Basic import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.Refl
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*);
static const lean_string_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2;
static const lean_array_object l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3 = (const lean_object*)&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 126, 228, 214, 96, 108, 195, 201)}};
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 154, 190, 235, 71, 53, 215, 0)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
static lean_once_cell_t l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deltaLHSUntilFix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 223, 150, 107, 82, 172, 43, 154)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "rwFixUnder: unexpected expression "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lfp_monotone_fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 113, 187, 250, 69, 106, 19, 81)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value),LEAN_SCALAR_PTR_LITERAL(83, 197, 58, 21, 58, 52, 66, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Elab.PreDefinition.PartialFixpoint.Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Eqns.0.Lean.Elab.PartialFixpoint.rwFixEq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "mkUnfoldEq rfl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkUnfoldEq after rwFixEq:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkUnfoldEq after deltaLHS:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to generate unfold theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkUnfoldEq start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_10_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3));
v___x_11_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2);
v___x_12_ = lean_box(0);
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_11_);
lean_ctor_set(v___x_14_, 3, v___x_11_);
lean_ctor_set(v___x_14_, 4, v___x_10_);
lean_ctor_set(v___x_14_, 5, v___x_13_);
lean_ctor_set(v___x_14_, 6, v___x_9_);
lean_ctor_set(v___x_14_, 7, v___x_10_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
return v___x_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_17_, lean_object* v_n_18_, lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; lean_object* v___x_21_; 
v___x_20_ = 0;
v___x_21_ = l_Lean_Environment_find_x3f(v_env_17_, v_n_18_, v___x_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
return v___x_20_;
}
else
{
lean_object* v_val_22_; uint8_t v___x_23_; 
v_val_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_val_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = l_Lean_ConstantInfo_hasValue(v_val_22_, v___x_20_);
lean_dec(v_val_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_24_, lean_object* v_n_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(v_env_24_, v_n_25_, v_x_26_);
lean_dec_ref(v_x_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v_k_31_; lean_object* v_v_32_; lean_object* v_l_33_; lean_object* v_r_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_k_31_ = lean_ctor_get(v_x_30_, 1);
v_v_32_ = lean_ctor_get(v_x_30_, 2);
v_l_33_ = lean_ctor_get(v_x_30_, 3);
v_r_34_ = lean_ctor_get(v_x_30_, 4);
v___x_35_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_29_, v_l_33_);
lean_inc(v_v_32_);
lean_inc(v_k_31_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_k_31_);
lean_ctor_set(v___x_36_, 1, v_v_32_);
v___x_37_ = lean_array_push(v___x_35_, v___x_36_);
v_init_29_ = v___x_37_;
v_x_30_ = v_r_34_;
goto _start;
}
else
{
return v_init_29_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_39_, v_x_40_);
lean_dec(v_x_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_44_, lean_object* v_s_45_, uint8_t v_x_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_47_ = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_47_, 0, v_env_44_);
v___x_48_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_47_, v_s_45_);
v___x_49_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_50_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v___x_49_, v___x_48_);
lean_dec(v___x_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_51_, lean_object* v_s_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_x_232__boxed_54_; lean_object* v_res_55_; 
v_x_232__boxed_54_ = lean_unbox(v_x_53_);
v_res_55_ = l_Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(v_env_51_, v_s_52_, v_x_232__boxed_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___f_69_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_70_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_71_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_));
v___x_72_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_70_, v___x_71_, v___f_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object* v_init_75_, lean_object* v_t_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_75_, v_t_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_78_, lean_object* v_t_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2__spec__0(v_init_78_, v_t_79_);
lean_dec(v_t_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_81_, uint8_t v___x_82_, uint8_t v_____do__lift_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
if (v_____do__lift_83_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(v___x_81_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(v___x_82_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_93_, lean_object* v___x_94_, lean_object* v_____do__lift_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
uint8_t v___x_4104__boxed_101_; uint8_t v___x_4105__boxed_102_; uint8_t v_____do__lift_4106__boxed_103_; lean_object* v_res_104_; 
v___x_4104__boxed_101_ = lean_unbox(v___x_93_);
v___x_4105__boxed_102_ = lean_unbox(v___x_94_);
v_____do__lift_4106__boxed_103_ = lean_unbox(v_____do__lift_95_);
v_res_104_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4104__boxed_101_, v___x_4105__boxed_102_, v_____do__lift_4106__boxed_103_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_104_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_105_, size_t v_i_106_, size_t v_stop_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_eq(v_i_106_, v_stop_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v_kind_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_array_uget_borrowed(v_as_105_, v_i_106_);
v_kind_110_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*9);
v___x_111_ = 1;
v___x_112_ = l_Lean_Elab_DefKind_isTheorem(v_kind_110_);
if (v___x_112_ == 0)
{
return v___x_111_;
}
else
{
if (v___x_108_ == 0)
{
size_t v___x_113_; size_t v___x_114_; 
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_106_, v___x_113_);
v_i_106_ = v___x_114_;
goto _start;
}
else
{
return v___x_111_;
}
}
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_stop_119_){
_start:
{
size_t v_i_boxed_120_; size_t v_stop_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_i_boxed_120_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_stop_boxed_121_ = lean_unbox_usize(v_stop_119_);
lean_dec(v_stop_119_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_117_, v_i_boxed_120_, v_stop_boxed_121_);
lean_dec_ref(v_as_117_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_124_, lean_object* v_declNameNonRec_125_, lean_object* v_fixedParamPerms_126_, lean_object* v_fixpointType_127_, lean_object* v_as_128_, size_t v_i_129_, size_t v_stop_130_, lean_object* v_b_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = lean_usize_dec_eq(v_i_129_, v_stop_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v_levelParams_134_; lean_object* v_declName_135_; lean_object* v_type_136_; lean_object* v_value_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; size_t v___x_141_; size_t v___x_142_; 
v___x_133_ = lean_array_uget_borrowed(v_as_128_, v_i_129_);
v_levelParams_134_ = lean_ctor_get(v___x_133_, 1);
v_declName_135_ = lean_ctor_get(v___x_133_, 3);
v_type_136_ = lean_ctor_get(v___x_133_, 6);
v_value_137_ = lean_ctor_get(v___x_133_, 7);
v___x_138_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc_ref(v_fixpointType_127_);
lean_inc_ref(v_fixedParamPerms_126_);
lean_inc(v_declNameNonRec_125_);
lean_inc_ref(v___x_124_);
lean_inc_ref(v_value_137_);
lean_inc_ref(v_type_136_);
lean_inc(v_levelParams_134_);
lean_inc(v_declName_135_);
v___x_139_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_139_, 0, v_declName_135_);
lean_ctor_set(v___x_139_, 1, v_levelParams_134_);
lean_ctor_set(v___x_139_, 2, v_type_136_);
lean_ctor_set(v___x_139_, 3, v_value_137_);
lean_ctor_set(v___x_139_, 4, v___x_124_);
lean_ctor_set(v___x_139_, 5, v_declNameNonRec_125_);
lean_ctor_set(v___x_139_, 6, v_fixedParamPerms_126_);
lean_ctor_set(v___x_139_, 7, v_fixpointType_127_);
lean_inc(v_declName_135_);
v___x_140_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_138_, v_b_131_, v_declName_135_, v___x_139_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_add(v_i_129_, v___x_141_);
v_i_129_ = v___x_142_;
v_b_131_ = v___x_140_;
goto _start;
}
else
{
lean_dec_ref(v_fixpointType_127_);
lean_dec_ref(v_fixedParamPerms_126_);
lean_dec(v_declNameNonRec_125_);
lean_dec_ref(v___x_124_);
return v_b_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_144_, lean_object* v_declNameNonRec_145_, lean_object* v_fixedParamPerms_146_, lean_object* v_fixpointType_147_, lean_object* v_as_148_, lean_object* v_i_149_, lean_object* v_stop_150_, lean_object* v_b_151_){
_start:
{
size_t v_i_boxed_152_; size_t v_stop_boxed_153_; lean_object* v_res_154_; 
v_i_boxed_152_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_stop_boxed_153_ = lean_unbox_usize(v_stop_150_);
lean_dec(v_stop_150_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_144_, v_declNameNonRec_145_, v_fixedParamPerms_146_, v_fixpointType_147_, v_as_148_, v_i_boxed_152_, v_stop_boxed_153_, v_b_151_);
lean_dec_ref(v_as_148_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_155_, size_t v_i_156_, lean_object* v_bs_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_usize_dec_lt(v_i_156_, v_sz_155_);
if (v___x_158_ == 0)
{
return v_bs_157_;
}
else
{
lean_object* v_v_159_; lean_object* v_declName_160_; lean_object* v___x_161_; lean_object* v_bs_x27_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
v_v_159_ = lean_array_uget_borrowed(v_bs_157_, v_i_156_);
v_declName_160_ = lean_ctor_get(v_v_159_, 3);
lean_inc(v_declName_160_);
v___x_161_ = lean_unsigned_to_nat(0u);
v_bs_x27_162_ = lean_array_uset(v_bs_157_, v_i_156_, v___x_161_);
v___x_163_ = ((size_t)1ULL);
v___x_164_ = lean_usize_add(v_i_156_, v___x_163_);
v___x_165_ = lean_array_uset(v_bs_x27_162_, v_i_156_, v_declName_160_);
v_i_156_ = v___x_164_;
v_bs_157_ = v___x_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_167_, lean_object* v_i_168_, lean_object* v_bs_169_){
_start:
{
size_t v_sz_boxed_170_; size_t v_i_boxed_171_; lean_object* v_res_172_; 
v_sz_boxed_170_ = lean_unbox_usize(v_sz_167_);
lean_dec(v_sz_167_);
v_i_boxed_171_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_res_172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_170_, v_i_boxed_171_, v_bs_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_usize_dec_eq(v_i_174_, v_stop_175_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v_declName_182_; lean_object* v___x_183_; 
v___x_181_ = lean_array_uget_borrowed(v_as_173_, v_i_174_);
v_declName_182_ = lean_ctor_get(v___x_181_, 3);
lean_inc(v_declName_182_);
v___x_183_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_182_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; size_t v___x_185_; size_t v___x_186_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_174_, v___x_185_);
v_i_174_ = v___x_186_;
v_b_176_ = v_a_184_;
goto _start;
}
else
{
return v___x_183_;
}
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_b_176_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_stop_191_, lean_object* v_b_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
size_t v_i_boxed_196_; size_t v_stop_boxed_197_; lean_object* v_res_198_; 
v_i_boxed_196_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_stop_boxed_197_ = lean_unbox_usize(v_stop_191_);
lean_dec(v_stop_191_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_189_, v_i_boxed_196_, v_stop_boxed_197_, v_b_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_as_189_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_199_, lean_object* v_as_200_, size_t v_i_201_, size_t v_stop_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_eq(v_i_201_, v_stop_202_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v_type_214_; uint8_t v___x_215_; uint8_t v_a_217_; lean_object* v___x_220_; 
v___x_213_ = lean_array_uget_borrowed(v_as_200_, v_i_201_);
v_type_214_ = lean_ctor_get(v___x_213_, 6);
v___x_215_ = 1;
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc_ref(v_type_214_);
v___x_220_ = l_Lean_Meta_isProp(v_type_214_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; uint8_t v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = lean_unbox(v_a_221_);
lean_dec(v_a_221_);
if (v___x_222_ == 0)
{
v_a_217_ = v___x_199_;
goto v___jp_216_;
}
else
{
goto v___jp_208_;
}
}
else
{
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_223_; uint8_t v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_220_);
v___x_224_ = lean_unbox(v_a_223_);
lean_dec(v_a_223_);
v_a_217_ = v___x_224_;
goto v___jp_216_;
}
else
{
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v___x_220_;
}
}
v___jp_216_:
{
if (v_a_217_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
v___x_218_ = lean_box(v___x_215_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
else
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
v___x_225_ = 0;
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
v___jp_208_:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_201_, v___x_209_);
v_i_201_ = v___x_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_stop_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v___x_4209__boxed_237_; size_t v_i_boxed_238_; size_t v_stop_boxed_239_; lean_object* v_res_240_; 
v___x_4209__boxed_237_ = lean_unbox(v___x_228_);
v_i_boxed_238_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_stop_boxed_239_ = lean_unbox_usize(v_stop_231_);
lean_dec(v_stop_231_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4209__boxed_237_, v_as_229_, v_i_boxed_238_, v_stop_boxed_239_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec_ref(v_as_229_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
lean_ctor_set(v___x_247_, 4, v___x_246_);
lean_ctor_set(v___x_247_, 5, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_248_, lean_object* v_declNameNonRec_249_, lean_object* v_fixedParamPerms_250_, lean_object* v_fixpointType_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_nextMacroScope_261_; lean_object* v_ngen_262_; lean_object* v_auxDeclNGen_263_; lean_object* v_traceState_264_; lean_object* v_messages_265_; lean_object* v_infoState_266_; lean_object* v_snapshotTasks_267_; lean_object* v___y_268_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___y_295_; lean_object* v___y_336_; uint8_t v___x_337_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_preDefs_248_);
v___x_337_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_337_ == 0)
{
goto v___jp_324_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_339_ == 0)
{
if (v___x_337_ == 0)
{
goto v___jp_324_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_293_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_248_, v___x_340_, v___x_341_, v___x_338_, v_a_254_, v_a_255_);
v___y_336_ = v___x_342_;
goto v___jp_335_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_293_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_248_, v___x_343_, v___x_344_, v___x_338_, v_a_254_, v_a_255_);
v___y_336_ = v___x_345_;
goto v___jp_335_;
}
}
v___jp_257_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_mctx_273_; lean_object* v_zetaDeltaFVarIds_274_; lean_object* v_postponed_275_; lean_object* v_diag_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_287_; 
v___x_269_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
v___x_270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v_nextMacroScope_261_);
lean_ctor_set(v___x_270_, 2, v_ngen_262_);
lean_ctor_set(v___x_270_, 3, v_auxDeclNGen_263_);
lean_ctor_set(v___x_270_, 4, v_traceState_264_);
lean_ctor_set(v___x_270_, 5, v___x_269_);
lean_ctor_set(v___x_270_, 6, v_messages_265_);
lean_ctor_set(v___x_270_, 7, v_infoState_266_);
lean_ctor_set(v___x_270_, 8, v_snapshotTasks_267_);
v___x_271_ = lean_st_ref_set(v_a_255_, v___x_270_);
lean_dec(v_a_255_);
v___x_272_ = lean_st_ref_take(v_a_253_);
v_mctx_273_ = lean_ctor_get(v___x_272_, 0);
v_zetaDeltaFVarIds_274_ = lean_ctor_get(v___x_272_, 2);
v_postponed_275_ = lean_ctor_get(v___x_272_, 3);
v_diag_276_ = lean_ctor_get(v___x_272_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_272_, 1);
lean_dec(v_unused_288_);
v___x_278_ = v___x_272_;
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_diag_276_);
lean_inc(v_postponed_275_);
lean_inc(v_zetaDeltaFVarIds_274_);
lean_inc(v_mctx_273_);
lean_dec(v___x_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_mctx_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_zetaDeltaFVarIds_274_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_postponed_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_diag_276_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_st_ref_set(v_a_253_, v___x_282_);
lean_dec(v_a_253_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
v___jp_294_:
{
if (lean_obj_tag(v___y_295_) == 0)
{
lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_296_ = lean_ctor_get(v___y_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___y_295_);
v___x_297_ = lean_unbox(v_a_296_);
lean_dec(v_a_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v_env_299_; lean_object* v_nextMacroScope_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_traceState_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; uint8_t v___x_307_; 
v___x_298_ = lean_st_ref_take(v_a_255_);
v_env_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc_ref(v_env_299_);
v_nextMacroScope_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_nextMacroScope_300_);
v_ngen_301_ = lean_ctor_get(v___x_298_, 2);
lean_inc_ref(v_ngen_301_);
v_auxDeclNGen_302_ = lean_ctor_get(v___x_298_, 3);
lean_inc_ref(v_auxDeclNGen_302_);
v_traceState_303_ = lean_ctor_get(v___x_298_, 4);
lean_inc_ref(v_traceState_303_);
v_messages_304_ = lean_ctor_get(v___x_298_, 6);
lean_inc_ref(v_messages_304_);
v_infoState_305_ = lean_ctor_get(v___x_298_, 7);
lean_inc_ref(v_infoState_305_);
v_snapshotTasks_306_ = lean_ctor_get(v___x_298_, 8);
lean_inc_ref(v_snapshotTasks_306_);
lean_dec(v___x_298_);
v___x_307_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v_env_299_;
goto v___jp_260_;
}
else
{
size_t v_sz_308_; size_t v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_sz_308_ = lean_array_size(v_preDefs_248_);
v___x_309_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_248_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_308_, v___x_309_, v_preDefs_248_);
v___x_311_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_311_ == 0)
{
if (v___x_307_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v_env_299_;
goto v___jp_260_;
}
else
{
size_t v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_usize_of_nat(v___x_293_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_310_, v_declNameNonRec_249_, v_fixedParamPerms_250_, v_fixpointType_251_, v_preDefs_248_, v___x_309_, v___x_312_, v_env_299_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v___x_313_;
goto v___jp_260_;
}
}
else
{
size_t v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_usize_of_nat(v___x_293_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_310_, v_declNameNonRec_249_, v_fixedParamPerms_250_, v_fixpointType_251_, v_preDefs_248_, v___x_309_, v___x_314_, v_env_299_);
lean_dec_ref(v_preDefs_248_);
v_nextMacroScope_261_ = v_nextMacroScope_300_;
v_ngen_262_ = v_ngen_301_;
v_auxDeclNGen_263_ = v_auxDeclNGen_302_;
v_traceState_264_ = v_traceState_303_;
v_messages_265_ = v_messages_304_;
v_infoState_266_ = v_infoState_305_;
v_snapshotTasks_267_ = v_snapshotTasks_306_;
v___y_268_ = v___x_315_;
goto v___jp_260_;
}
}
}
else
{
lean_dec(v_a_255_);
lean_dec(v_a_253_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_257_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_a_255_);
lean_dec(v_a_253_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
v_a_316_ = lean_ctor_get(v___y_295_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___y_295_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___y_295_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___y_295_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
v___jp_324_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_325_ == 0)
{
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
if (v___x_325_ == 0)
{
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
size_t v___x_326_; size_t v___x_327_; uint8_t v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_293_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_248_, v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_289_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
if (v___x_325_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_328_, v___x_329_, v___x_329_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_252_);
v___y_295_ = v___x_330_;
goto v___jp_294_;
}
else
{
if (v___x_325_ == 0)
{
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
goto v___jp_257_;
}
else
{
lean_object* v___x_331_; 
lean_inc(v_a_255_);
lean_inc_ref(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_328_, v_preDefs_248_, v___x_326_, v___x_327_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_unbox(v_a_332_);
lean_dec(v_a_332_);
v___x_334_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_328_, v___x_329_, v___x_333_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_252_);
v___y_295_ = v___x_334_;
goto v___jp_294_;
}
else
{
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_252_);
v___y_295_ = v___x_331_;
goto v___jp_294_;
}
}
}
}
}
}
}
v___jp_335_:
{
if (lean_obj_tag(v___y_336_) == 0)
{
lean_dec_ref(v___y_336_);
goto v___jp_324_;
}
else
{
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_fixpointType_251_);
lean_dec_ref(v_fixedParamPerms_250_);
lean_dec(v_declNameNonRec_249_);
lean_dec_ref(v_preDefs_248_);
return v___y_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_346_, lean_object* v_declNameNonRec_347_, lean_object* v_fixedParamPerms_348_, lean_object* v_fixpointType_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_346_, v_declNameNonRec_347_, v_fixedParamPerms_348_, v_fixpointType_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_, lean_object* v_b_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_356_, v_i_357_, v_stop_358_, v_b_359_, v___y_362_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_366_, v_i_boxed_375_, v_stop_boxed_376_, v_b_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec_ref(v_as_366_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_378_, lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_378_, v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_385_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_385_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
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
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_410_, lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_419_, lean_object* v_mvarId_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_419_, v_mvarId_420_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_428_, lean_object* v_declNameNonRec_429_, lean_object* v_n_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_name_eq(v_n_430_, v_declName_428_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = lean_name_eq(v_n_430_, v_declNameNonRec_429_);
return v___x_432_;
}
else
{
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_433_, lean_object* v_declNameNonRec_434_, lean_object* v_n_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_433_, v_declNameNonRec_434_, v_n_435_);
lean_dec(v_n_435_);
lean_dec(v_declNameNonRec_434_);
lean_dec(v_declName_433_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_448_ = l_Lean_MessageData_ofFormat(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_451_, lean_object* v___f_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v_mvarId_451_);
v___x_458_ = l_Lean_MVarId_getType_x27(v_mvarId_451_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = l_Lean_Expr_isAppOfArity(v_a_459_, v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_a_459_);
lean_dec_ref(v___f_452_);
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_464_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_465_ = l_Lean_Meta_throwTacticEx___redArg(v___x_463_, v_mvarId_451_, v___x_464_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_Expr_appFn_x21(v_a_459_);
v___x_467_ = l_Lean_Expr_appArg_x21(v___x_466_);
lean_dec_ref(v___x_466_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
v___x_468_ = l_Lean_Meta_deltaExpand(v___x_467_, v___f_452_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v___x_470_ = l_Lean_Expr_appArg_x21(v_a_459_);
lean_dec(v_a_459_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
v___x_471_ = l_Lean_Meta_mkEq(v_a_469_, v___x_470_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_473_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_451_, v_a_472_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_473_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_mvarId_451_);
v_a_474_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_471_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_a_459_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_mvarId_451_);
v_a_482_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_468_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v___f_452_);
lean_dec(v_mvarId_451_);
v_a_490_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_458_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_458_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_498_, lean_object* v___f_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_498_, v___f_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_506_, lean_object* v_declNameNonRec_507_, lean_object* v_mvarId_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v___f_514_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_514_, 0, v_declName_506_);
lean_closure_set(v___f_514_, 1, v_declNameNonRec_507_);
lean_inc(v_mvarId_508_);
v___f_515_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_515_, 0, v_mvarId_508_);
lean_closure_set(v___f_515_, 1, v___f_514_);
v___x_516_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_508_, v___f_515_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_517_, lean_object* v_declNameNonRec_518_, lean_object* v_mvarId_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_517_, v_declNameNonRec_518_, v_mvarId_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object* v_msg_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = l_Lean_instInhabitedExpr;
v___x_528_ = lean_panic_fn(v___x_527_, v_msg_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object* v_msgData_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_env_536_; lean_object* v___x_537_; lean_object* v_mctx_538_; lean_object* v_lctx_539_; lean_object* v_options_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_535_ = lean_st_ref_get(v___y_533_);
v_env_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_env_536_);
lean_dec(v___x_535_);
v___x_537_ = lean_st_ref_get(v___y_531_);
v_mctx_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc_ref(v_mctx_538_);
lean_dec(v___x_537_);
v_lctx_539_ = lean_ctor_get(v___y_530_, 2);
v_options_540_ = lean_ctor_get(v___y_532_, 2);
lean_inc_ref(v_options_540_);
lean_inc_ref(v_lctx_539_);
v___x_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_541_, 0, v_env_536_);
lean_ctor_set(v___x_541_, 1, v_mctx_538_);
lean_ctor_set(v___x_541_, 2, v_lctx_539_);
lean_ctor_set(v___x_541_, 3, v_options_540_);
v___x_542_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_msgData_529_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object* v_msgData_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object* v_msg_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_ref_557_; lean_object* v___x_558_; lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_ref_557_ = lean_ctor_get(v___y_554_, 5);
v___x_558_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_inc(v_ref_557_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_ref_557_);
lean_ctor_set(v___x_563_, 1, v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 1);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_574_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_588_ = l_Lean_stringToMessageData(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l_Lean_Expr_bvar___override(v___x_595_);
return v___x_596_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12(void){
_start:
{
lean_object* v___x_597_; size_t v___x_598_; 
v___x_597_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_598_ = lean_ptr_addr(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15));
v___x_603_ = lean_unsigned_to_nat(18u);
v___x_604_ = lean_unsigned_to_nat(1872u);
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14));
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_607_ = l_mkPanicMessageWithDecl(v___x_606_, v___x_605_, v___x_604_, v___x_603_, v___x_602_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21(void){
_start:
{
lean_object* v___x_616_; lean_object* v_dummy_617_; 
v___x_616_ = lean_box(0);
v_dummy_617_ = l_Lean_Expr_sort___override(v___x_616_);
return v_dummy_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2));
v___x_630_ = lean_unsigned_to_nat(4u);
v___x_631_ = l_Lean_Expr_isAppOfArity(v_lhs_623_, v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4));
v___x_633_ = l_Lean_Expr_isAppOfArity(v_lhs_623_, v___x_632_, v___x_630_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = l_Lean_Expr_isApp(v_lhs_623_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_Expr_isProj(v_lhs_623_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_637_ = l_Lean_MessageData_ofExpr(v_lhs_623_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_638_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = l_Lean_Expr_projExpr_x21(v_lhs_623_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc_ref(v___x_640_);
v___x_641_ = lean_infer_type(v___x_640_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
v___x_643_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_640_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v___y_648_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_646_ = 0;
if (lean_obj_tag(v_lhs_623_) == 11)
{
lean_object* v_typeName_656_; lean_object* v_idx_657_; lean_object* v_struct_658_; lean_object* v___x_659_; size_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v_typeName_656_ = lean_ctor_get(v_lhs_623_, 0);
v_idx_657_ = lean_ctor_get(v_lhs_623_, 1);
v_struct_658_ = lean_ctor_get(v_lhs_623_, 2);
v___x_659_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_660_ = lean_ptr_addr(v_struct_658_);
v___x_661_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
v___x_662_ = lean_usize_dec_eq(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_inc(v_idx_657_);
lean_inc(v_typeName_656_);
lean_dec_ref(v_lhs_623_);
v___x_663_ = l_Lean_Expr_proj___override(v_typeName_656_, v_idx_657_, v___x_659_);
v___y_648_ = v___x_663_;
goto v___jp_647_;
}
else
{
v___y_648_ = v_lhs_623_;
goto v___jp_647_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v_lhs_623_);
v___x_664_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
v___x_665_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_664_);
v___y_648_ = v___x_665_;
goto v___jp_647_;
}
v___jp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_649_ = l_Lean_mkLambda(v___x_645_, v___x_646_, v_a_642_, v___y_648_);
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_651_ = lean_unsigned_to_nat(2u);
v___x_652_ = lean_mk_empty_array_with_capacity(v___x_651_);
v___x_653_ = lean_array_push(v___x_652_, v___x_649_);
v___x_654_ = lean_array_push(v___x_653_, v_a_644_);
v___x_655_ = l_Lean_Meta_mkAppM(v___x_650_, v___x_654_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_655_;
}
}
else
{
lean_dec(v_a_642_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec_ref(v_lhs_623_);
return v___x_643_;
}
}
else
{
lean_dec_ref(v___x_640_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec_ref(v_lhs_623_);
return v___x_641_;
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = l_Lean_Expr_appFn_x21(v_lhs_623_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
v___x_667_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_666_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18));
v___x_670_ = l_Lean_Expr_appArg_x21(v_lhs_623_);
lean_dec_ref(v_lhs_623_);
v___x_671_ = lean_unsigned_to_nat(2u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_array_push(v___x_672_, v_a_668_);
v___x_674_ = lean_array_push(v___x_673_, v___x_670_);
v___x_675_ = l_Lean_Meta_mkAppM(v___x_669_, v___x_674_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_675_;
}
else
{
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec_ref(v_lhs_623_);
return v___x_667_;
}
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_dummy_680_; lean_object* v_nargs_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20));
v___x_677_ = l_Lean_Expr_getAppFn(v_lhs_623_);
v___x_678_ = l_Lean_Expr_constLevels_x21(v___x_677_);
lean_dec_ref(v___x_677_);
v___x_679_ = l_Lean_mkConst(v___x_676_, v___x_678_);
v_dummy_680_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_681_ = l_Lean_Expr_getAppNumArgs(v_lhs_623_);
lean_inc(v_nargs_681_);
v___x_682_ = lean_mk_array(v_nargs_681_, v_dummy_680_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_sub(v_nargs_681_, v___x_683_);
lean_dec(v_nargs_681_);
v___x_685_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_623_, v___x_682_, v___x_684_);
v___x_686_ = l_Lean_mkAppN(v___x_679_, v___x_685_);
lean_dec_ref(v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_dummy_692_; lean_object* v_nargs_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23));
v___x_689_ = l_Lean_Expr_getAppFn(v_lhs_623_);
v___x_690_ = l_Lean_Expr_constLevels_x21(v___x_689_);
lean_dec_ref(v___x_689_);
v___x_691_ = l_Lean_mkConst(v___x_688_, v___x_690_);
v_dummy_692_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_693_ = l_Lean_Expr_getAppNumArgs(v_lhs_623_);
lean_inc(v_nargs_693_);
v___x_694_ = lean_mk_array(v_nargs_693_, v_dummy_692_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_sub(v_nargs_693_, v___x_695_);
lean_dec(v_nargs_693_);
v___x_697_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_623_, v___x_694_, v___x_696_);
v___x_698_ = l_Lean_mkAppN(v___x_691_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_00_u03b1_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object* v_00_u03b1_715_, lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_715_, v_msg_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___f_730_; lean_object* v___x_1569__overap_731_; lean_object* v___x_732_; 
v___f_730_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1569__overap_731_ = lean_panic_fn(v___f_730_, v_msg_724_);
v___x_732_ = lean_apply_5(v___x_1569__overap_731_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, lean_box(0));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_ks_744_; lean_object* v_vs_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_769_; 
v_ks_744_ = lean_ctor_get(v_x_740_, 0);
v_vs_745_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_769_ == 0)
{
v___x_747_ = v_x_740_;
v_isShared_748_ = v_isSharedCheck_769_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_vs_745_);
lean_inc(v_ks_744_);
lean_dec(v_x_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_769_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_ks_744_);
v___x_750_ = lean_nat_dec_lt(v_x_741_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_x_741_);
v___x_751_ = lean_array_push(v_ks_744_, v_x_742_);
v___x_752_ = lean_array_push(v_vs_745_, v_x_743_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_752_);
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v_k_x27_756_; uint8_t v___x_757_; 
v_k_x27_756_ = lean_array_fget_borrowed(v_ks_744_, v_x_741_);
v___x_757_ = l_Lean_instBEqMVarId_beq(v_x_742_, v_k_x27_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_759_; 
if (v_isShared_748_ == 0)
{
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_ks_744_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_vs_745_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_x_741_, v___x_760_);
lean_dec(v_x_741_);
v_x_740_ = v___x_759_;
v_x_741_ = v___x_761_;
goto _start;
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_764_ = lean_array_fset(v_ks_744_, v_x_741_, v_x_742_);
v___x_765_ = lean_array_fset(v_vs_745_, v_x_741_, v_x_743_);
lean_dec(v_x_741_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_765_);
lean_ctor_set(v___x_747_, 0, v___x_764_);
v___x_767_ = v___x_747_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_770_, lean_object* v_k_771_, lean_object* v_v_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_770_, v___x_773_, v_k_771_, v_v_772_);
return v___x_774_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; 
v___x_775_ = ((size_t)5ULL);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_shift_left(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_780_ = lean_usize_sub(v___x_779_, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_782_, size_t v_x_783_, size_t v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v_es_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_es_787_ = lean_ctor_get(v_x_782_, 0);
v___x_788_ = ((size_t)5ULL);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_791_ = lean_usize_land(v_x_783_, v___x_790_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get_size(v_es_787_);
v___x_794_ = lean_nat_dec_lt(v_j_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_dec(v_j_792_);
lean_dec(v_x_786_);
lean_dec(v_x_785_);
return v_x_782_;
}
else
{
lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_831_; 
lean_inc_ref(v_es_787_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_x_782_, 0);
lean_dec(v_unused_832_);
v___x_796_ = v_x_782_;
v_isShared_797_ = v_isSharedCheck_831_;
goto v_resetjp_795_;
}
else
{
lean_dec(v_x_782_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_831_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_v_798_; lean_object* v___x_799_; lean_object* v_xs_x27_800_; lean_object* v___y_802_; 
v_v_798_ = lean_array_fget(v_es_787_, v_j_792_);
v___x_799_ = lean_box(0);
v_xs_x27_800_ = lean_array_fset(v_es_787_, v_j_792_, v___x_799_);
switch(lean_obj_tag(v_v_798_))
{
case 0:
{
lean_object* v_key_807_; lean_object* v_val_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_818_; 
v_key_807_ = lean_ctor_get(v_v_798_, 0);
v_val_808_ = lean_ctor_get(v_v_798_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_v_798_);
if (v_isSharedCheck_818_ == 0)
{
v___x_810_ = v_v_798_;
v_isShared_811_ = v_isSharedCheck_818_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_val_808_);
lean_inc(v_key_807_);
lean_dec(v_v_798_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_818_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = l_Lean_instBEqMVarId_beq(v_x_785_, v_key_807_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_810_);
v___x_813_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_807_, v_val_808_, v_x_785_, v_x_786_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___y_802_ = v___x_814_;
goto v___jp_801_;
}
else
{
lean_object* v___x_816_; 
lean_dec(v_val_808_);
lean_dec(v_key_807_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_x_786_);
lean_ctor_set(v___x_810_, 0, v_x_785_);
v___x_816_ = v___x_810_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_x_785_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_x_786_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v___y_802_ = v___x_816_;
goto v___jp_801_;
}
}
}
}
case 1:
{
lean_object* v_node_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_829_; 
v_node_819_ = lean_ctor_get(v_v_798_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_v_798_);
if (v_isSharedCheck_829_ == 0)
{
v___x_821_ = v_v_798_;
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_node_819_);
lean_dec(v_v_798_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_823_ = lean_usize_shift_right(v_x_783_, v___x_788_);
v___x_824_ = lean_usize_add(v_x_784_, v___x_789_);
v___x_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_819_, v___x_823_, v___x_824_, v_x_785_, v_x_786_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_825_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v___y_802_ = v___x_827_;
goto v___jp_801_;
}
}
}
default: 
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_x_785_);
lean_ctor_set(v___x_830_, 1, v_x_786_);
v___y_802_ = v___x_830_;
goto v___jp_801_;
}
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_array_fset(v_xs_x27_800_, v_j_792_, v___y_802_);
lean_dec(v_j_792_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_803_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_854_; 
v_ks_833_ = lean_ctor_get(v_x_782_, 0);
v_vs_834_ = lean_ctor_get(v_x_782_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_854_ == 0)
{
v___x_836_ = v_x_782_;
v_isShared_837_ = v_isSharedCheck_854_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_vs_834_);
lean_inc(v_ks_833_);
lean_dec(v_x_782_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_854_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_ks_833_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_vs_834_);
v___x_839_ = v_reuseFailAlloc_853_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v_newNode_840_; uint8_t v___y_842_; size_t v___x_848_; uint8_t v___x_849_; 
v_newNode_840_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_839_, v_x_785_, v_x_786_);
v___x_848_ = ((size_t)7ULL);
v___x_849_ = lean_usize_dec_le(v___x_848_, v_x_784_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_840_);
v___x_851_ = lean_unsigned_to_nat(4u);
v___x_852_ = lean_nat_dec_lt(v___x_850_, v___x_851_);
lean_dec(v___x_850_);
v___y_842_ = v___x_852_;
goto v___jp_841_;
}
else
{
v___y_842_ = v___x_849_;
goto v___jp_841_;
}
v___jp_841_:
{
if (v___y_842_ == 0)
{
lean_object* v_ks_843_; lean_object* v_vs_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_ks_843_ = lean_ctor_get(v_newNode_840_, 0);
lean_inc_ref(v_ks_843_);
v_vs_844_ = lean_ctor_get(v_newNode_840_, 1);
lean_inc_ref(v_vs_844_);
lean_dec_ref(v_newNode_840_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_784_, v_ks_843_, v_vs_844_, v___x_845_, v___x_846_);
lean_dec_ref(v_vs_844_);
lean_dec_ref(v_ks_843_);
return v___x_847_;
}
else
{
return v_newNode_840_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_855_, lean_object* v_keys_856_, lean_object* v_vals_857_, lean_object* v_i_858_, lean_object* v_entries_859_){
_start:
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_array_get_size(v_keys_856_);
v___x_861_ = lean_nat_dec_lt(v_i_858_, v___x_860_);
if (v___x_861_ == 0)
{
lean_dec(v_i_858_);
return v_entries_859_;
}
else
{
lean_object* v_k_862_; lean_object* v_v_863_; uint64_t v___x_864_; size_t v_h_865_; size_t v___x_866_; lean_object* v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v_h_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_k_862_ = lean_array_fget_borrowed(v_keys_856_, v_i_858_);
v_v_863_ = lean_array_fget_borrowed(v_vals_857_, v_i_858_);
v___x_864_ = l_Lean_instHashableMVarId_hash(v_k_862_);
v_h_865_ = lean_uint64_to_usize(v___x_864_);
v___x_866_ = ((size_t)5ULL);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_sub(v_depth_855_, v___x_868_);
v___x_870_ = lean_usize_mul(v___x_866_, v___x_869_);
v_h_871_ = lean_usize_shift_right(v_h_865_, v___x_870_);
v___x_872_ = lean_nat_add(v_i_858_, v___x_867_);
lean_dec(v_i_858_);
lean_inc(v_v_863_);
lean_inc(v_k_862_);
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_859_, v_h_871_, v_depth_855_, v_k_862_, v_v_863_);
v_i_858_ = v___x_872_;
v_entries_859_ = v___x_873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_875_, lean_object* v_keys_876_, lean_object* v_vals_877_, lean_object* v_i_878_, lean_object* v_entries_879_){
_start:
{
size_t v_depth_boxed_880_; lean_object* v_res_881_; 
v_depth_boxed_880_ = lean_unbox_usize(v_depth_875_);
lean_dec(v_depth_875_);
v_res_881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_880_, v_keys_876_, v_vals_877_, v_i_878_, v_entries_879_);
lean_dec_ref(v_vals_877_);
lean_dec_ref(v_keys_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
size_t v_x_2154__boxed_887_; size_t v_x_2155__boxed_888_; lean_object* v_res_889_; 
v_x_2154__boxed_887_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_x_2155__boxed_888_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_882_, v_x_2154__boxed_887_, v_x_2155__boxed_888_, v_x_885_, v_x_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
uint64_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
v___x_893_ = l_Lean_instHashableMVarId_hash(v_x_891_);
v___x_894_ = lean_uint64_to_usize(v___x_893_);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_890_, v___x_894_, v___x_895_, v_x_891_, v_x_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_897_, lean_object* v_val_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; lean_object* v_mctx_902_; lean_object* v_cache_903_; lean_object* v_zetaDeltaFVarIds_904_; lean_object* v_postponed_905_; lean_object* v_diag_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_933_; 
v___x_901_ = lean_st_ref_take(v___y_899_);
v_mctx_902_ = lean_ctor_get(v___x_901_, 0);
v_cache_903_ = lean_ctor_get(v___x_901_, 1);
v_zetaDeltaFVarIds_904_ = lean_ctor_get(v___x_901_, 2);
v_postponed_905_ = lean_ctor_get(v___x_901_, 3);
v_diag_906_ = lean_ctor_get(v___x_901_, 4);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_933_ == 0)
{
v___x_908_ = v___x_901_;
v_isShared_909_ = v_isSharedCheck_933_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_diag_906_);
lean_inc(v_postponed_905_);
lean_inc(v_zetaDeltaFVarIds_904_);
lean_inc(v_cache_903_);
lean_inc(v_mctx_902_);
lean_dec(v___x_901_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_933_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_depth_910_; lean_object* v_levelAssignDepth_911_; lean_object* v_mvarCounter_912_; lean_object* v_lDepth_913_; lean_object* v_decls_914_; lean_object* v_userNames_915_; lean_object* v_lAssignment_916_; lean_object* v_eAssignment_917_; lean_object* v_dAssignment_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_932_; 
v_depth_910_ = lean_ctor_get(v_mctx_902_, 0);
v_levelAssignDepth_911_ = lean_ctor_get(v_mctx_902_, 1);
v_mvarCounter_912_ = lean_ctor_get(v_mctx_902_, 2);
v_lDepth_913_ = lean_ctor_get(v_mctx_902_, 3);
v_decls_914_ = lean_ctor_get(v_mctx_902_, 4);
v_userNames_915_ = lean_ctor_get(v_mctx_902_, 5);
v_lAssignment_916_ = lean_ctor_get(v_mctx_902_, 6);
v_eAssignment_917_ = lean_ctor_get(v_mctx_902_, 7);
v_dAssignment_918_ = lean_ctor_get(v_mctx_902_, 8);
v_isSharedCheck_932_ = !lean_is_exclusive(v_mctx_902_);
if (v_isSharedCheck_932_ == 0)
{
v___x_920_ = v_mctx_902_;
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_dAssignment_918_);
lean_inc(v_eAssignment_917_);
lean_inc(v_lAssignment_916_);
lean_inc(v_userNames_915_);
lean_inc(v_decls_914_);
lean_inc(v_lDepth_913_);
lean_inc(v_mvarCounter_912_);
lean_inc(v_levelAssignDepth_911_);
lean_inc(v_depth_910_);
lean_dec(v_mctx_902_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_917_, v_mvarId_897_, v_val_898_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 7, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_depth_910_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_levelAssignDepth_911_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_mvarCounter_912_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_lDepth_913_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_decls_914_);
lean_ctor_set(v_reuseFailAlloc_931_, 5, v_userNames_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 6, v_lAssignment_916_);
lean_ctor_set(v_reuseFailAlloc_931_, 7, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 8, v_dAssignment_918_);
v___x_924_ = v_reuseFailAlloc_931_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_924_);
v___x_926_ = v___x_908_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_cache_903_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_zetaDeltaFVarIds_904_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_postponed_905_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_diag_906_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_st_ref_set(v___y_899_, v___x_926_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_934_, lean_object* v_val_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_934_, v_val_935_, v___y_936_);
lean_dec(v___y_936_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_943_ = lean_unsigned_to_nat(41u);
v___x_944_ = lean_unsigned_to_nat(68u);
v___x_945_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_947_ = l_mkPanicMessageWithDecl(v___x_946_, v___x_945_, v___x_944_, v___x_943_, v___x_942_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_949_ = lean_unsigned_to_nat(51u);
v___x_950_ = lean_unsigned_to_nat(70u);
v___x_951_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_953_ = l_mkPanicMessageWithDecl(v___x_952_, v___x_951_, v___x_950_, v___x_949_, v___x_948_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v_mvarId_954_);
v___x_960_ = l_Lean_MVarId_getType_x27(v_mvarId_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = l_Lean_Expr_isAppOfArity(v_a_961_, v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_a_961_);
lean_dec(v_mvarId_954_);
v___x_965_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_966_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_965_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = l_Lean_Expr_appFn_x21(v_a_961_);
v___x_968_ = l_Lean_Expr_appArg_x21(v___x_967_);
lean_dec_ref(v___x_967_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
v___x_969_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_968_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v_a_970_);
v___x_971_ = lean_infer_type(v_a_970_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; uint8_t v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Expr_isAppOfArity(v_a_972_, v___x_962_, v___x_963_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_a_972_);
lean_dec(v_a_970_);
lean_dec(v_a_961_);
lean_dec(v_mvarId_954_);
v___x_974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_975_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_974_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_Expr_appArg_x21(v_a_961_);
lean_dec(v_a_961_);
v___x_977_ = l_Lean_Expr_appArg_x21(v_a_972_);
lean_dec(v_a_972_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
v___x_978_ = l_Lean_Meta_mkEq(v___x_977_, v___x_976_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_box(0);
lean_inc_ref(v___y_955_);
v___x_981_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_979_, v___x_980_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
lean_inc(v___y_956_);
lean_inc(v_a_982_);
v___x_983_ = l_Lean_Meta_mkEqTrans(v_a_970_, v_a_982_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_954_, v_a_984_, v___y_956_);
lean_dec(v___y_956_);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_994_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Lean_Expr_mvarId_x21(v_a_982_);
lean_dec(v_a_982_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_982_);
lean_dec(v___y_956_);
lean_dec(v_mvarId_954_);
v_a_995_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_983_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_983_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_970_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_954_);
v_a_1003_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_981_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_981_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_a_970_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_954_);
v_a_1011_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_978_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_978_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_970_);
lean_dec(v_a_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_954_);
v_a_1019_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_971_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_971_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_954_);
v_a_1027_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_969_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_969_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_954_);
v_a_1035_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_960_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_960_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; 
lean_inc(v_mvarId_1050_);
v___f_1056_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1056_, 0, v_mvarId_1050_);
v___x_1057_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1050_, v___f_1056_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1065_, lean_object* v_val_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1065_, v_val_1066_, v___y_1068_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1073_, lean_object* v_val_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1073_, v_val_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, size_t v_x_1088_, size_t v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_2652__boxed_1099_; size_t v_x_2653__boxed_1100_; lean_object* v_res_1101_; 
v_x_2652__boxed_1099_ = lean_unbox_usize(v_x_1095_);
lean_dec(v_x_1095_);
v_x_2653__boxed_1100_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_res_1101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1093_, v_x_1094_, v_x_2652__boxed_1099_, v_x_2653__boxed_1100_, v_x_1097_, v_x_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1102_, lean_object* v_n_1103_, lean_object* v_k_1104_, lean_object* v_v_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1103_, v_k_1104_, v_v_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1107_, size_t v_depth_1108_, lean_object* v_keys_1109_, lean_object* v_vals_1110_, lean_object* v_heq_1111_, lean_object* v_i_1112_, lean_object* v_entries_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1108_, v_keys_1109_, v_vals_1110_, v_i_1112_, v_entries_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1115_, lean_object* v_depth_1116_, lean_object* v_keys_1117_, lean_object* v_vals_1118_, lean_object* v_heq_1119_, lean_object* v_i_1120_, lean_object* v_entries_1121_){
_start:
{
size_t v_depth_boxed_1122_; lean_object* v_res_1123_; 
v_depth_boxed_1122_ = lean_unbox_usize(v_depth_1116_);
lean_dec(v_depth_1116_);
v_res_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1115_, v_depth_boxed_1122_, v_keys_1117_, v_vals_1118_, v_heq_1119_, v_i_1120_, v_entries_1121_);
lean_dec_ref(v_vals_1118_);
lean_dec_ref(v_keys_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1125_, v_x_1126_, v_x_1127_, v_x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_cls_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_options_1136_; uint8_t v_hasTrace_1137_; 
v_options_1136_ = lean_ctor_get(v___y_1134_, 2);
v_hasTrace_1137_ = lean_ctor_get_uint8(v_options_1136_, sizeof(void*)*1);
if (v_hasTrace_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_cls_1133_);
v___x_1138_ = lean_box(v_hasTrace_1137_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v_inheritedTraceOptions_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_inheritedTraceOptions_1140_ = lean_ctor_get(v___y_1134_, 13);
v___x_1141_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1));
v___x_1142_ = l_Lean_Name_append(v___x_1141_, v_cls_1133_);
v___x_1143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1140_, v_options_1136_, v___x_1142_);
lean_dec(v___x_1142_);
v___x_1144_ = lean_box(v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_cls_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v_cls_1146_, v___y_1147_);
lean_dec_ref(v___y_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v_cls_1150_, v___y_1153_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1164_, lean_object* v_opt_1165_){
_start:
{
lean_object* v_name_1166_; lean_object* v_defValue_1167_; lean_object* v_map_1168_; lean_object* v___x_1169_; 
v_name_1166_ = lean_ctor_get(v_opt_1165_, 0);
v_defValue_1167_ = lean_ctor_get(v_opt_1165_, 1);
v_map_1168_ = lean_ctor_get(v_opts_1164_, 0);
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1168_, v_name_1166_);
if (lean_obj_tag(v___x_1169_) == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_unbox(v_defValue_1167_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; 
v_val_1171_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___x_1169_);
if (lean_obj_tag(v_val_1171_) == 1)
{
uint8_t v_v_1172_; 
v_v_1172_ = lean_ctor_get_uint8(v_val_1171_, 0);
lean_dec_ref(v_val_1171_);
return v_v_1172_;
}
else
{
uint8_t v___x_1173_; 
lean_dec(v_val_1171_);
v___x_1173_ = lean_unbox(v_defValue_1167_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1174_, lean_object* v_opt_1175_){
_start:
{
uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_res_1176_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1174_, v_opt_1175_);
lean_dec_ref(v_opt_1175_);
lean_dec_ref(v_opts_1174_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_opts_1178_, lean_object* v_opt_1179_){
_start:
{
lean_object* v_name_1180_; lean_object* v_defValue_1181_; lean_object* v_map_1182_; lean_object* v___x_1183_; 
v_name_1180_ = lean_ctor_get(v_opt_1179_, 0);
v_defValue_1181_ = lean_ctor_get(v_opt_1179_, 1);
v_map_1182_ = lean_ctor_get(v_opts_1178_, 0);
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1182_, v_name_1180_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_inc(v_defValue_1181_);
return v_defValue_1181_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref(v___x_1183_);
if (lean_obj_tag(v_val_1184_) == 3)
{
lean_object* v_v_1185_; 
v_v_1185_ = lean_ctor_get(v_val_1184_, 0);
lean_inc(v_v_1185_);
lean_dec_ref(v_val_1184_);
return v_v_1185_;
}
else
{
lean_dec(v_val_1184_);
lean_inc(v_defValue_1181_);
return v_defValue_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_opts_1186_, lean_object* v_opt_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_opts_1186_, v_opt_1187_);
lean_dec_ref(v_opt_1187_);
lean_dec_ref(v_opts_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(lean_object* v_e_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Lean_Expr_hasMVar(v_e_1189_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_e_1189_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v_mctx_1195_; lean_object* v___x_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1199_; lean_object* v_cache_1200_; lean_object* v_zetaDeltaFVarIds_1201_; lean_object* v_postponed_1202_; lean_object* v_diag_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1212_; 
v___x_1194_ = lean_st_ref_get(v___y_1190_);
v_mctx_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_ref(v_mctx_1195_);
lean_dec(v___x_1194_);
v___x_1196_ = l_Lean_instantiateMVarsCore(v_mctx_1195_, v_e_1189_);
v_fst_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_fst_1197_);
v_snd_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_snd_1198_);
lean_dec_ref(v___x_1196_);
v___x_1199_ = lean_st_ref_take(v___y_1190_);
v_cache_1200_ = lean_ctor_get(v___x_1199_, 1);
v_zetaDeltaFVarIds_1201_ = lean_ctor_get(v___x_1199_, 2);
v_postponed_1202_ = lean_ctor_get(v___x_1199_, 3);
v_diag_1203_ = lean_ctor_get(v___x_1199_, 4);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v___x_1199_, 0);
lean_dec(v_unused_1213_);
v___x_1205_ = v___x_1199_;
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_diag_1203_);
lean_inc(v_postponed_1202_);
lean_inc(v_zetaDeltaFVarIds_1201_);
lean_inc(v_cache_1200_);
lean_dec(v___x_1199_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_snd_1198_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_snd_1198_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_cache_1200_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_zetaDeltaFVarIds_1201_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_postponed_1202_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_diag_1203_);
v___x_1208_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_st_ref_set(v___y_1190_, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_fst_1197_);
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg___boxed(lean_object* v_e_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_e_1214_, v___y_1215_);
lean_dec(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object* v_e_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_e_1218_, v___y_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object* v_e_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_e_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object* v_k_1232_, uint8_t v_allowLevelAssignments_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1233_, v_k_1232_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1239_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1239_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object* v_k_1256_, lean_object* v_allowLevelAssignments_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1263_; lean_object* v_res_1264_; 
v_allowLevelAssignments_boxed_1263_ = lean_unbox(v_allowLevelAssignments_1257_);
v_res_1264_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_k_1256_, v_allowLevelAssignments_boxed_1263_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object* v_00_u03b1_1265_, lean_object* v_k_1266_, uint8_t v_allowLevelAssignments_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_k_1266_, v_allowLevelAssignments_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_k_1275_, lean_object* v_allowLevelAssignments_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1282_; lean_object* v_res_1283_; 
v_allowLevelAssignments_boxed_1282_ = lean_unbox(v_allowLevelAssignments_1276_);
v_res_1283_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_00_u03b1_1274_, v_k_1275_, v_allowLevelAssignments_boxed_1282_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object* v_thm_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_env_1288_; lean_object* v_toConstantVal_1289_; lean_object* v_value_1290_; lean_object* v_all_1291_; uint8_t v___y_1293_; lean_object* v_type_1301_; uint8_t v___x_1302_; 
v___x_1287_ = lean_st_ref_get(v___y_1285_);
v_env_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc_ref(v_env_1288_);
lean_dec(v___x_1287_);
v_toConstantVal_1289_ = lean_ctor_get(v_thm_1284_, 0);
v_value_1290_ = lean_ctor_get(v_thm_1284_, 1);
v_all_1291_ = lean_ctor_get(v_thm_1284_, 2);
v_type_1301_ = lean_ctor_get(v_toConstantVal_1289_, 2);
lean_inc_ref(v_env_1288_);
v___x_1302_ = l_Lean_Environment_hasUnsafe(v_env_1288_, v_type_1301_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_Environment_hasUnsafe(v_env_1288_, v_value_1290_);
v___y_1293_ = v___x_1303_;
goto v___jp_1292_;
}
else
{
lean_dec_ref(v_env_1288_);
v___y_1293_ = v___x_1302_;
goto v___jp_1292_;
}
v___jp_1292_:
{
if (v___y_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_thm_1284_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_inc(v_all_1291_);
lean_inc_ref(v_value_1290_);
lean_inc_ref(v_toConstantVal_1289_);
lean_dec_ref(v_thm_1284_);
v___x_1296_ = lean_box(0);
v___x_1297_ = 0;
v___x_1298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1298_, 0, v_toConstantVal_1289_);
lean_ctor_set(v___x_1298_, 1, v_value_1290_);
lean_ctor_set(v___x_1298_, 2, v___x_1296_);
lean_ctor_set(v___x_1298_, 3, v_all_1291_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*4, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object* v_thm_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_thm_1304_, v___y_1305_);
lean_dec(v___y_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object* v_thm_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_thm_1308_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object* v_thm_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_thm_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(lean_object* v_k_1322_, lean_object* v_b_1323_, lean_object* v_c_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_apply_7(v_k_1322_, v_b_1323_, v_c_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, lean_box(0));
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed(lean_object* v_k_1331_, lean_object* v_b_1332_, lean_object* v_c_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0(v_k_1331_, v_b_1332_, v_c_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(lean_object* v_e_1340_, lean_object* v_k_1341_, uint8_t v_cleanupAnnotations_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___f_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1348_, 0, v_k_1341_);
v___x_1349_ = 1;
v___x_1350_ = 0;
v___x_1351_ = lean_box(0);
v___x_1352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1340_, v___x_1349_, v___x_1350_, v___x_1349_, v___x_1350_, v___x_1351_, v___f_1348_, v_cleanupAnnotations_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg___boxed(lean_object* v_e_1369_, lean_object* v_k_1370_, lean_object* v_cleanupAnnotations_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1377_; lean_object* v_res_1378_; 
v_cleanupAnnotations_boxed_1377_ = lean_unbox(v_cleanupAnnotations_1371_);
v_res_1378_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_e_1369_, v_k_1370_, v_cleanupAnnotations_boxed_1377_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(lean_object* v_00_u03b1_1379_, lean_object* v_e_1380_, lean_object* v_k_1381_, uint8_t v_cleanupAnnotations_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_e_1380_, v_k_1381_, v_cleanupAnnotations_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_e_1390_, lean_object* v_k_1391_, lean_object* v_cleanupAnnotations_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1398_; lean_object* v_res_1399_; 
v_cleanupAnnotations_boxed_1398_ = lean_unbox(v_cleanupAnnotations_1392_);
v_res_1399_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9(v_00_u03b1_1389_, v_e_1390_, v_k_1391_, v_cleanupAnnotations_boxed_1398_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(lean_object* v_o_1400_, lean_object* v_k_1401_, uint8_t v_v_1402_){
_start:
{
lean_object* v_map_1403_; uint8_t v_hasTrace_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1418_; 
v_map_1403_ = lean_ctor_get(v_o_1400_, 0);
v_hasTrace_1404_ = lean_ctor_get_uint8(v_o_1400_, sizeof(void*)*1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_o_1400_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1406_ = v_o_1400_;
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_map_1403_);
lean_dec(v_o_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1408_, 0, v_v_1402_);
lean_inc(v_k_1401_);
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1401_, v___x_1408_, v_map_1403_);
if (v_hasTrace_1404_ == 0)
{
lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1413_; 
v___x_1410_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg___closed__1));
v___x_1411_ = l_Lean_Name_isPrefixOf(v___x_1410_, v_k_1401_);
lean_dec(v_k_1401_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1409_);
v___x_1413_ = v___x_1406_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1409_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*1, v___x_1411_);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_k_1401_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1409_);
v___x_1416_ = v___x_1406_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1417_, sizeof(void*)*1, v_hasTrace_1404_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2___boxed(lean_object* v_o_1419_, lean_object* v_k_1420_, lean_object* v_v_1421_){
_start:
{
uint8_t v_v_boxed_1422_; lean_object* v_res_1423_; 
v_v_boxed_1422_ = lean_unbox(v_v_1421_);
v_res_1423_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(v_o_1419_, v_k_1420_, v_v_boxed_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1424_, lean_object* v_opt_1425_, uint8_t v_val_1426_){
_start:
{
lean_object* v_name_1427_; lean_object* v___x_1428_; 
v_name_1427_ = lean_ctor_get(v_opt_1425_, 0);
lean_inc(v_name_1427_);
lean_dec_ref(v_opt_1425_);
v___x_1428_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2_spec__2(v_opts_1424_, v_name_1427_, v_val_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1429_, lean_object* v_opt_1430_, lean_object* v_val_1431_){
_start:
{
uint8_t v_val_boxed_1432_; lean_object* v_res_1433_; 
v_val_boxed_1432_ = lean_unbox(v_val_1431_);
v_res_1433_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1429_, v_opt_1430_, v_val_boxed_1432_);
return v_res_1433_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1434_; double v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_float_of_nat(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1492_; 
v_ref_1446_ = lean_ctor_get(v___y_1443_, 5);
v___x_1447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v_traceState_1453_; lean_object* v_env_1454_; lean_object* v_nextMacroScope_1455_; lean_object* v_ngen_1456_; lean_object* v_auxDeclNGen_1457_; lean_object* v_cache_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1491_; 
v___x_1452_ = lean_st_ref_take(v___y_1444_);
v_traceState_1453_ = lean_ctor_get(v___x_1452_, 4);
v_env_1454_ = lean_ctor_get(v___x_1452_, 0);
v_nextMacroScope_1455_ = lean_ctor_get(v___x_1452_, 1);
v_ngen_1456_ = lean_ctor_get(v___x_1452_, 2);
v_auxDeclNGen_1457_ = lean_ctor_get(v___x_1452_, 3);
v_cache_1458_ = lean_ctor_get(v___x_1452_, 5);
v_messages_1459_ = lean_ctor_get(v___x_1452_, 6);
v_infoState_1460_ = lean_ctor_get(v___x_1452_, 7);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1452_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_cache_1458_);
lean_inc(v_traceState_1453_);
lean_inc(v_auxDeclNGen_1457_);
lean_inc(v_ngen_1456_);
lean_inc(v_nextMacroScope_1455_);
lean_inc(v_env_1454_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint64_t v_tid_1465_; lean_object* v_traces_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_tid_1465_ = lean_ctor_get_uint64(v_traceState_1453_, sizeof(void*)*1);
v_traces_1466_ = lean_ctor_get(v_traceState_1453_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_traceState_1453_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v_traceState_1453_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_traces_1466_);
lean_dec(v_traceState_1453_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; double v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__0);
v___x_1472_ = 0;
v___x_1473_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__1));
v___x_1474_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1474_, 0, v_cls_1439_);
lean_ctor_set(v___x_1474_, 1, v___x_1470_);
lean_ctor_set(v___x_1474_, 2, v___x_1473_);
lean_ctor_set_float(v___x_1474_, sizeof(void*)*3, v___x_1471_);
lean_ctor_set_float(v___x_1474_, sizeof(void*)*3 + 8, v___x_1471_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*3 + 16, v___x_1472_);
v___x_1475_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___closed__2));
v___x_1476_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v_a_1448_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
lean_inc(v_ref_1446_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_ref_1446_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_PersistentArray_push___redArg(v_traces_1466_, v___x_1477_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1478_);
v___x_1480_ = v___x_1468_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1478_);
lean_ctor_set_uint64(v_reuseFailAlloc_1489_, sizeof(void*)*1, v_tid_1465_);
v___x_1480_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1480_);
v___x_1482_ = v___x_1463_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_env_1454_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_nextMacroScope_1455_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_ngen_1456_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_auxDeclNGen_1457_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_cache_1458_);
lean_ctor_set(v_reuseFailAlloc_1488_, 6, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1488_, 7, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1488_, 8, v_snapshotTasks_1461_);
v___x_1482_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = lean_st_ref_set(v___y_1444_, v___x_1482_);
v___x_1484_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1484_);
v___x_1486_ = v___x_1450_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_cls_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v_declName_1510_, lean_object* v_declNameNonRec_1511_, lean_object* v___x_1512_, lean_object* v___x_1513_, lean_object* v_a_1514_, lean_object* v_____r_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; uint8_t v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; uint8_t v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v_fileName_1531_; lean_object* v_fileMap_1532_; lean_object* v_currRecDepth_1533_; lean_object* v_ref_1534_; lean_object* v_currNamespace_1535_; lean_object* v_openDecls_1536_; lean_object* v_initHeartbeats_1537_; lean_object* v_maxHeartbeats_1538_; lean_object* v_quotContext_1539_; lean_object* v_currMacroScope_1540_; lean_object* v_cancelTk_x3f_1541_; uint8_t v_suppressElabErrors_1542_; lean_object* v_inheritedTraceOptions_1543_; lean_object* v___y_1544_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v___y_1602_; uint8_t v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___x_1713_; 
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
v___x_1713_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1510_, v_declNameNonRec_1511_, v___x_1512_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1771_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
lean_inc(v___x_1513_);
v___x_1751_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1513_, v___y_1518_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1771_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1771_;
goto v_resetjp_1753_;
}
v___jp_1715_:
{
lean_object* v___x_1720_; 
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
v___x_1720_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1714_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1742_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
lean_inc(v___x_1513_);
v___x_1722_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1513_, v___y_1718_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1742_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1742_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
if (v___x_1727_ == 0)
{
lean_del_object(v___x_1725_);
v___y_1703_ = v_a_1721_;
v___y_1704_ = v___y_1716_;
v___y_1705_ = v___y_1717_;
v___y_1706_ = v___y_1718_;
v___y_1707_ = v___y_1719_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3);
lean_inc(v_a_1721_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 1);
lean_ctor_set(v___x_1725_, 0, v_a_1721_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1721_);
v___x_1730_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
lean_inc(v___x_1513_);
v___x_1732_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1513_, v___x_1731_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_dec_ref(v___x_1732_);
v___y_1703_ = v_a_1721_;
v___y_1704_ = v___y_1716_;
v___y_1705_ = v___y_1717_;
v___y_1706_ = v___y_1718_;
v___y_1707_ = v___y_1719_;
goto v___jp_1702_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1721_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_a_1514_);
lean_dec(v___x_1513_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
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
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_a_1514_);
lean_dec(v___x_1513_);
v_a_1743_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1720_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1720_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
v_resetjp_1753_:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_unbox(v_a_1752_);
lean_dec(v_a_1752_);
if (v___x_1756_ == 0)
{
lean_del_object(v___x_1754_);
v___y_1716_ = v___y_1516_;
v___y_1717_ = v___y_1517_;
v___y_1718_ = v___y_1518_;
v___y_1719_ = v___y_1519_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5);
lean_inc(v_a_1714_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 1);
lean_ctor_set(v___x_1754_, 0, v_a_1714_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1714_);
v___x_1759_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
lean_inc(v___x_1513_);
v___x_1761_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1513_, v___x_1760_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_dec_ref(v___x_1761_);
v___y_1716_ = v___y_1516_;
v___y_1717_ = v___y_1517_;
v___y_1718_ = v___y_1518_;
v___y_1719_ = v___y_1519_;
goto v___jp_1715_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1714_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_a_1514_);
lean_dec(v___x_1513_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_a_1514_);
lean_dec(v___x_1513_);
v_a_1772_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1713_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1713_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
v___jp_1521_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1545_ = l_Lean_maxRecDepth;
v___x_1546_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v___y_1526_, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1547_, 0, v_fileName_1531_);
lean_ctor_set(v___x_1547_, 1, v_fileMap_1532_);
lean_ctor_set(v___x_1547_, 2, v___y_1526_);
lean_ctor_set(v___x_1547_, 3, v_currRecDepth_1533_);
lean_ctor_set(v___x_1547_, 4, v___x_1546_);
lean_ctor_set(v___x_1547_, 5, v_ref_1534_);
lean_ctor_set(v___x_1547_, 6, v_currNamespace_1535_);
lean_ctor_set(v___x_1547_, 7, v_openDecls_1536_);
lean_ctor_set(v___x_1547_, 8, v_initHeartbeats_1537_);
lean_ctor_set(v___x_1547_, 9, v_maxHeartbeats_1538_);
lean_ctor_set(v___x_1547_, 10, v_quotContext_1539_);
lean_ctor_set(v___x_1547_, 11, v_currMacroScope_1540_);
lean_ctor_set(v___x_1547_, 12, v_cancelTk_x3f_1541_);
lean_ctor_set(v___x_1547_, 13, v_inheritedTraceOptions_1543_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*14, v___y_1525_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*14 + 1, v_suppressElabErrors_1542_);
lean_inc(v___y_1530_);
v___x_1548_ = l_Lean_MVarId_refl(v___y_1522_, v___y_1528_, v___y_1527_, v___y_1530_, v___x_1547_, v___y_1544_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; lean_object* v_a_1550_; uint8_t v___x_1551_; 
lean_dec_ref(v___x_1548_);
lean_inc(v___x_1513_);
v___x_1549_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1513_, v___y_1524_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = lean_unbox(v_a_1550_);
lean_dec(v_a_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec_ref(v___y_1529_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v___x_1513_);
v___x_1552_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_a_1514_, v___y_1530_);
lean_dec(v___y_1530_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1);
v___x_1554_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1513_, v___x_1553_, v___y_1529_, v___y_1530_, v___y_1524_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v___y_1529_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v___x_1554_);
v___x_1555_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___redArg(v_a_1514_, v___y_1530_);
lean_dec(v___y_1530_);
return v___x_1555_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v___y_1530_);
lean_dec_ref(v_a_1514_);
v_a_1556_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1554_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v_a_1514_);
lean_dec(v___x_1513_);
v_a_1564_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1548_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1548_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
v___jp_1572_:
{
lean_object* v_fileName_1584_; lean_object* v_fileMap_1585_; lean_object* v_currRecDepth_1586_; lean_object* v_ref_1587_; lean_object* v_currNamespace_1588_; lean_object* v_openDecls_1589_; lean_object* v_initHeartbeats_1590_; lean_object* v_maxHeartbeats_1591_; lean_object* v_quotContext_1592_; lean_object* v_currMacroScope_1593_; lean_object* v_cancelTk_x3f_1594_; uint8_t v_suppressElabErrors_1595_; lean_object* v_inheritedTraceOptions_1596_; 
v_fileName_1584_ = lean_ctor_get(v___y_1582_, 0);
lean_inc_ref(v_fileName_1584_);
v_fileMap_1585_ = lean_ctor_get(v___y_1582_, 1);
lean_inc_ref(v_fileMap_1585_);
v_currRecDepth_1586_ = lean_ctor_get(v___y_1582_, 3);
lean_inc(v_currRecDepth_1586_);
v_ref_1587_ = lean_ctor_get(v___y_1582_, 5);
lean_inc(v_ref_1587_);
v_currNamespace_1588_ = lean_ctor_get(v___y_1582_, 6);
lean_inc(v_currNamespace_1588_);
v_openDecls_1589_ = lean_ctor_get(v___y_1582_, 7);
lean_inc(v_openDecls_1589_);
v_initHeartbeats_1590_ = lean_ctor_get(v___y_1582_, 8);
lean_inc(v_initHeartbeats_1590_);
v_maxHeartbeats_1591_ = lean_ctor_get(v___y_1582_, 9);
lean_inc(v_maxHeartbeats_1591_);
v_quotContext_1592_ = lean_ctor_get(v___y_1582_, 10);
lean_inc(v_quotContext_1592_);
v_currMacroScope_1593_ = lean_ctor_get(v___y_1582_, 11);
lean_inc(v_currMacroScope_1593_);
v_cancelTk_x3f_1594_ = lean_ctor_get(v___y_1582_, 12);
lean_inc(v_cancelTk_x3f_1594_);
v_suppressElabErrors_1595_ = lean_ctor_get_uint8(v___y_1582_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1596_ = lean_ctor_get(v___y_1582_, 13);
lean_inc_ref(v_inheritedTraceOptions_1596_);
lean_dec_ref(v___y_1582_);
v___y_1522_ = v___y_1573_;
v___y_1523_ = v___y_1574_;
v___y_1524_ = v___y_1575_;
v___y_1525_ = v___y_1576_;
v___y_1526_ = v___y_1577_;
v___y_1527_ = v___y_1578_;
v___y_1528_ = v___y_1579_;
v___y_1529_ = v___y_1580_;
v___y_1530_ = v___y_1581_;
v_fileName_1531_ = v_fileName_1584_;
v_fileMap_1532_ = v_fileMap_1585_;
v_currRecDepth_1533_ = v_currRecDepth_1586_;
v_ref_1534_ = v_ref_1587_;
v_currNamespace_1535_ = v_currNamespace_1588_;
v_openDecls_1536_ = v_openDecls_1589_;
v_initHeartbeats_1537_ = v_initHeartbeats_1590_;
v_maxHeartbeats_1538_ = v_maxHeartbeats_1591_;
v_quotContext_1539_ = v_quotContext_1592_;
v_currMacroScope_1540_ = v_currMacroScope_1593_;
v_cancelTk_x3f_1541_ = v_cancelTk_x3f_1594_;
v_suppressElabErrors_1542_ = v_suppressElabErrors_1595_;
v_inheritedTraceOptions_1543_ = v_inheritedTraceOptions_1596_;
v___y_1544_ = v___y_1583_;
goto v___jp_1521_;
}
v___jp_1597_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_traceState_1613_; lean_object* v_messages_1614_; lean_object* v_infoState_1615_; lean_object* v_snapshotTasks_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v___x_1608_ = lean_st_ref_take(v___y_1599_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1608_, 3);
v_traceState_1613_ = lean_ctor_get(v___x_1608_, 4);
v_messages_1614_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1615_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1616_ = lean_ctor_get(v___x_1608_, 8);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1608_, 5);
lean_dec(v_unused_1627_);
v___x_1618_ = v___x_1608_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snapshotTasks_1616_);
lean_inc(v_infoState_1615_);
lean_inc(v_messages_1614_);
lean_inc(v_traceState_1613_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1608_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = l_Lean_Kernel_enableDiag(v_env_1609_, v___y_1601_);
v___x_1621_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 5, v___x_1621_);
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_traceState_1613_);
lean_ctor_set(v_reuseFailAlloc_1625_, 5, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1625_, 6, v_messages_1614_);
lean_ctor_set(v_reuseFailAlloc_1625_, 7, v_infoState_1615_);
lean_ctor_set(v_reuseFailAlloc_1625_, 8, v_snapshotTasks_1616_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_st_ref_set(v___y_1599_, v___x_1623_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
v___y_1573_ = v___y_1598_;
v___y_1574_ = v___y_1599_;
v___y_1575_ = v___y_1600_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1604_;
v___y_1579_ = v___y_1603_;
v___y_1580_ = v___y_1605_;
v___y_1581_ = v___y_1606_;
v___y_1582_ = v___y_1600_;
v___y_1583_ = v___y_1599_;
goto v___jp_1572_;
}
}
}
else
{
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
v___y_1573_ = v___y_1598_;
v___y_1574_ = v___y_1599_;
v___y_1575_ = v___y_1600_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1604_;
v___y_1579_ = v___y_1603_;
v___y_1580_ = v___y_1605_;
v___y_1581_ = v___y_1606_;
v___y_1582_ = v___y_1600_;
v___y_1583_ = v___y_1599_;
goto v___jp_1572_;
}
}
v___jp_1628_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v_foApprox_1638_; uint8_t v_ctxApprox_1639_; uint8_t v_quasiPatternApprox_1640_; uint8_t v_constApprox_1641_; uint8_t v_isDefEqStuckEx_1642_; uint8_t v_unificationHints_1643_; uint8_t v_proofIrrelevance_1644_; uint8_t v_assignSyntheticOpaque_1645_; uint8_t v_offsetCnstrs_1646_; uint8_t v_etaStruct_1647_; uint8_t v_univApprox_1648_; uint8_t v_iota_1649_; uint8_t v_beta_1650_; uint8_t v_proj_1651_; uint8_t v_zeta_1652_; uint8_t v_zetaDelta_1653_; uint8_t v_zetaUnused_1654_; uint8_t v_zetaHave_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1701_; 
v___x_1636_ = lean_st_ref_get(v___y_1630_);
v___x_1637_ = l_Lean_Meta_Context_config(v___y_1633_);
v_foApprox_1638_ = lean_ctor_get_uint8(v___x_1637_, 0);
v_ctxApprox_1639_ = lean_ctor_get_uint8(v___x_1637_, 1);
v_quasiPatternApprox_1640_ = lean_ctor_get_uint8(v___x_1637_, 2);
v_constApprox_1641_ = lean_ctor_get_uint8(v___x_1637_, 3);
v_isDefEqStuckEx_1642_ = lean_ctor_get_uint8(v___x_1637_, 4);
v_unificationHints_1643_ = lean_ctor_get_uint8(v___x_1637_, 5);
v_proofIrrelevance_1644_ = lean_ctor_get_uint8(v___x_1637_, 6);
v_assignSyntheticOpaque_1645_ = lean_ctor_get_uint8(v___x_1637_, 7);
v_offsetCnstrs_1646_ = lean_ctor_get_uint8(v___x_1637_, 8);
v_etaStruct_1647_ = lean_ctor_get_uint8(v___x_1637_, 10);
v_univApprox_1648_ = lean_ctor_get_uint8(v___x_1637_, 11);
v_iota_1649_ = lean_ctor_get_uint8(v___x_1637_, 12);
v_beta_1650_ = lean_ctor_get_uint8(v___x_1637_, 13);
v_proj_1651_ = lean_ctor_get_uint8(v___x_1637_, 14);
v_zeta_1652_ = lean_ctor_get_uint8(v___x_1637_, 15);
v_zetaDelta_1653_ = lean_ctor_get_uint8(v___x_1637_, 16);
v_zetaUnused_1654_ = lean_ctor_get_uint8(v___x_1637_, 17);
v_zetaHave_1655_ = lean_ctor_get_uint8(v___x_1637_, 18);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1657_ = v___x_1637_;
v_isShared_1658_ = v_isSharedCheck_1701_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v___x_1637_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1701_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint8_t v_trackZetaDelta_1659_; lean_object* v_zetaDeltaSet_1660_; lean_object* v_lctx_1661_; lean_object* v_localInstances_1662_; lean_object* v_defEqCtx_x3f_1663_; lean_object* v_synthPendingDepth_1664_; lean_object* v_canUnfold_x3f_1665_; uint8_t v_univApprox_1666_; uint8_t v_inTypeClassResolution_1667_; uint8_t v_cacheInferType_1668_; lean_object* v_fileName_1669_; lean_object* v_fileMap_1670_; lean_object* v_options_1671_; lean_object* v_currRecDepth_1672_; lean_object* v_ref_1673_; lean_object* v_currNamespace_1674_; lean_object* v_openDecls_1675_; lean_object* v_initHeartbeats_1676_; lean_object* v_maxHeartbeats_1677_; lean_object* v_quotContext_1678_; lean_object* v_currMacroScope_1679_; lean_object* v_cancelTk_x3f_1680_; uint8_t v_suppressElabErrors_1681_; lean_object* v_inheritedTraceOptions_1682_; lean_object* v_env_1683_; lean_object* v_config_1685_; 
v_trackZetaDelta_1659_ = lean_ctor_get_uint8(v___y_1633_, sizeof(void*)*7);
v_zetaDeltaSet_1660_ = lean_ctor_get(v___y_1633_, 1);
v_lctx_1661_ = lean_ctor_get(v___y_1633_, 2);
v_localInstances_1662_ = lean_ctor_get(v___y_1633_, 3);
v_defEqCtx_x3f_1663_ = lean_ctor_get(v___y_1633_, 4);
v_synthPendingDepth_1664_ = lean_ctor_get(v___y_1633_, 5);
v_canUnfold_x3f_1665_ = lean_ctor_get(v___y_1633_, 6);
v_univApprox_1666_ = lean_ctor_get_uint8(v___y_1633_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1667_ = lean_ctor_get_uint8(v___y_1633_, sizeof(void*)*7 + 2);
v_cacheInferType_1668_ = lean_ctor_get_uint8(v___y_1633_, sizeof(void*)*7 + 3);
v_fileName_1669_ = lean_ctor_get(v___y_1631_, 0);
v_fileMap_1670_ = lean_ctor_get(v___y_1631_, 1);
v_options_1671_ = lean_ctor_get(v___y_1631_, 2);
v_currRecDepth_1672_ = lean_ctor_get(v___y_1631_, 3);
v_ref_1673_ = lean_ctor_get(v___y_1631_, 5);
v_currNamespace_1674_ = lean_ctor_get(v___y_1631_, 6);
v_openDecls_1675_ = lean_ctor_get(v___y_1631_, 7);
v_initHeartbeats_1676_ = lean_ctor_get(v___y_1631_, 8);
v_maxHeartbeats_1677_ = lean_ctor_get(v___y_1631_, 9);
v_quotContext_1678_ = lean_ctor_get(v___y_1631_, 10);
v_currMacroScope_1679_ = lean_ctor_get(v___y_1631_, 11);
v_cancelTk_x3f_1680_ = lean_ctor_get(v___y_1631_, 12);
v_suppressElabErrors_1681_ = lean_ctor_get_uint8(v___y_1631_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1682_ = lean_ctor_get(v___y_1631_, 13);
v_env_1683_ = lean_ctor_get(v___x_1636_, 0);
lean_inc_ref(v_env_1683_);
lean_dec(v___x_1636_);
if (v_isShared_1658_ == 0)
{
v_config_1685_ = v___x_1657_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 0, v_foApprox_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 1, v_ctxApprox_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 2, v_quasiPatternApprox_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 3, v_constApprox_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 4, v_isDefEqStuckEx_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 5, v_unificationHints_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 6, v_proofIrrelevance_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 7, v_assignSyntheticOpaque_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 8, v_offsetCnstrs_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 10, v_etaStruct_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 11, v_univApprox_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 12, v_iota_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 13, v_beta_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 14, v_proj_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 15, v_zeta_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 16, v_zetaDelta_1653_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 17, v_zetaUnused_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, 18, v_zetaHave_1655_);
v_config_1685_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v_key_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; uint8_t v___x_1699_; 
lean_ctor_set_uint8(v_config_1685_, 9, v___y_1635_);
v___x_1686_ = l_Lean_Meta_Context_configKey(v___y_1633_);
v___x_1687_ = 2ULL;
v___x_1688_ = lean_uint64_shift_right(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_uint64_shift_left(v___x_1688_, v___x_1687_);
v___x_1690_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1635_);
v_key_1691_ = lean_uint64_lor(v___x_1689_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1692_, 0, v_config_1685_);
lean_ctor_set_uint64(v___x_1692_, sizeof(void*)*1, v_key_1691_);
lean_inc(v_canUnfold_x3f_1665_);
lean_inc(v_synthPendingDepth_1664_);
lean_inc(v_defEqCtx_x3f_1663_);
lean_inc_ref(v_localInstances_1662_);
lean_inc_ref(v_lctx_1661_);
lean_inc(v_zetaDeltaSet_1660_);
v___x_1693_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_zetaDeltaSet_1660_);
lean_ctor_set(v___x_1693_, 2, v_lctx_1661_);
lean_ctor_set(v___x_1693_, 3, v_localInstances_1662_);
lean_ctor_set(v___x_1693_, 4, v_defEqCtx_x3f_1663_);
lean_ctor_set(v___x_1693_, 5, v_synthPendingDepth_1664_);
lean_ctor_set(v___x_1693_, 6, v_canUnfold_x3f_1665_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7, v_trackZetaDelta_1659_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 1, v_univApprox_1666_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1667_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 3, v_cacheInferType_1668_);
v___x_1694_ = l_Lean_Meta_smartUnfolding;
v___x_1695_ = 0;
lean_inc_ref(v_options_1671_);
v___x_1696_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_options_1671_, v___x_1694_, v___x_1695_);
v___x_1697_ = l_Lean_diagnostics;
v___x_1698_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_1696_, v___x_1697_);
v___x_1699_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1683_);
lean_dec_ref(v_env_1683_);
if (v___x_1699_ == 0)
{
if (v___x_1698_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1682_);
lean_inc(v_cancelTk_x3f_1680_);
lean_inc(v_currMacroScope_1679_);
lean_inc(v_quotContext_1678_);
lean_inc(v_maxHeartbeats_1677_);
lean_inc(v_initHeartbeats_1676_);
lean_inc(v_openDecls_1675_);
lean_inc(v_currNamespace_1674_);
lean_inc(v_ref_1673_);
lean_inc(v_currRecDepth_1672_);
lean_inc_ref(v_fileMap_1670_);
lean_inc_ref(v_fileName_1669_);
lean_inc(v___y_1630_);
v___y_1522_ = v___y_1629_;
v___y_1523_ = v___y_1630_;
v___y_1524_ = v___y_1631_;
v___y_1525_ = v___x_1698_;
v___y_1526_ = v___x_1696_;
v___y_1527_ = v___x_1693_;
v___y_1528_ = v___y_1632_;
v___y_1529_ = v___y_1633_;
v___y_1530_ = v___y_1634_;
v_fileName_1531_ = v_fileName_1669_;
v_fileMap_1532_ = v_fileMap_1670_;
v_currRecDepth_1533_ = v_currRecDepth_1672_;
v_ref_1534_ = v_ref_1673_;
v_currNamespace_1535_ = v_currNamespace_1674_;
v_openDecls_1536_ = v_openDecls_1675_;
v_initHeartbeats_1537_ = v_initHeartbeats_1676_;
v_maxHeartbeats_1538_ = v_maxHeartbeats_1677_;
v_quotContext_1539_ = v_quotContext_1678_;
v_currMacroScope_1540_ = v_currMacroScope_1679_;
v_cancelTk_x3f_1541_ = v_cancelTk_x3f_1680_;
v_suppressElabErrors_1542_ = v_suppressElabErrors_1681_;
v_inheritedTraceOptions_1543_ = v_inheritedTraceOptions_1682_;
v___y_1544_ = v___y_1630_;
goto v___jp_1521_;
}
else
{
v___y_1598_ = v___y_1629_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___x_1698_;
v___y_1602_ = v___x_1696_;
v___y_1603_ = v___y_1632_;
v___y_1604_ = v___x_1693_;
v___y_1605_ = v___y_1633_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___x_1699_;
goto v___jp_1597_;
}
}
else
{
v___y_1598_ = v___y_1629_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___x_1698_;
v___y_1602_ = v___x_1696_;
v___y_1603_ = v___y_1632_;
v___y_1604_ = v___x_1693_;
v___y_1605_ = v___y_1633_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___x_1698_;
goto v___jp_1597_;
}
}
}
}
v___jp_1702_:
{
lean_object* v___x_1708_; uint8_t v_transparency_1709_; uint8_t v___x_1710_; uint8_t v___x_1711_; uint8_t v___x_1712_; 
v___x_1708_ = l_Lean_Meta_Context_config(v___y_1704_);
v_transparency_1709_ = lean_ctor_get_uint8(v___x_1708_, 9);
lean_dec_ref(v___x_1708_);
v___x_1710_ = 0;
v___x_1711_ = 1;
v___x_1712_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1709_, v___x_1710_);
if (v___x_1712_ == 0)
{
v___y_1629_ = v___y_1703_;
v___y_1630_ = v___y_1707_;
v___y_1631_ = v___y_1706_;
v___y_1632_ = v___x_1711_;
v___y_1633_ = v___y_1704_;
v___y_1634_ = v___y_1705_;
v___y_1635_ = v_transparency_1709_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v___y_1703_;
v___y_1630_ = v___y_1707_;
v___y_1631_ = v___y_1706_;
v___y_1632_ = v___x_1711_;
v___y_1633_ = v___y_1704_;
v___y_1634_ = v___y_1705_;
v___y_1635_ = v___x_1710_;
goto v___jp_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_declName_1780_, lean_object* v_declNameNonRec_1781_, lean_object* v___x_1782_, lean_object* v___x_1783_, lean_object* v_a_1784_, lean_object* v_____r_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1780_, v_declNameNonRec_1781_, v___x_1782_, v___x_1783_, v_a_1784_, v_____r_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v_res_1791_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_declName_1807_, lean_object* v_a_1808_, lean_object* v___x_1809_, lean_object* v_declNameNonRec_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1829_; lean_object* v_a_1830_; lean_object* v___y_1834_; lean_object* v___x_1836_; 
lean_inc_ref(v___y_1811_);
v___x_1836_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1808_, v___x_1809_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1864_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6));
v___x_1839_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___redArg(v___x_1838_, v___y_1813_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = l_Lean_Expr_mvarId_x21(v_a_1837_);
v___x_1845_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1842_);
v___x_1846_ = lean_box(0);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v_declName_1807_);
v___x_1847_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1807_, v_declNameNonRec_1810_, v___x_1844_, v___x_1838_, v_a_1837_, v___x_1846_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
v___y_1834_ = v___x_1847_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8);
lean_inc(v___x_1844_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 1);
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1850_ = v___x_1842_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1844_);
v___x_1850_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1848_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v___x_1838_, v___x_1851_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v_declName_1807_);
v___x_1854_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v_declName_1807_, v_declNameNonRec_1810_, v___x_1844_, v___x_1838_, v_a_1837_, v_a_1853_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
v___y_1834_ = v___x_1854_;
goto v___jp_1833_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v___x_1844_);
lean_dec(v_a_1837_);
lean_dec(v_declNameNonRec_1810_);
v_a_1855_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1852_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1852_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
lean_inc(v_a_1855_);
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
v___y_1829_ = v___x_1860_;
v_a_1830_ = v_a_1855_;
goto v___jp_1828_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1810_);
v___y_1834_ = v___x_1836_;
goto v___jp_1833_;
}
v___jp_1816_:
{
if (v___y_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v___y_1817_);
v___x_1820_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1821_ = l_Lean_MessageData_ofConstName(v_declName_1807_, v___y_1819_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_Exception_toMessageData(v___y_1818_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1826_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v___x_1827_;
}
else
{
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_declName_1807_);
return v___y_1817_;
}
}
v___jp_1828_:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Lean_Exception_isInterrupt(v_a_1830_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
lean_inc_ref(v_a_1830_);
v___x_1832_ = l_Lean_Exception_isRuntime(v_a_1830_);
v___y_1817_ = v___y_1829_;
v___y_1818_ = v_a_1830_;
v___y_1819_ = v___x_1832_;
goto v___jp_1816_;
}
else
{
v___y_1817_ = v___y_1829_;
v___y_1818_ = v_a_1830_;
v___y_1819_ = v___x_1831_;
goto v___jp_1816_;
}
}
v___jp_1833_:
{
if (lean_obj_tag(v___y_1834_) == 0)
{
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_declName_1807_);
return v___y_1834_;
}
else
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___y_1834_, 0);
lean_inc(v_a_1835_);
v___y_1829_ = v___y_1834_;
v_a_1830_ = v_a_1835_;
goto v___jp_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1865_, lean_object* v_a_1866_, lean_object* v___x_1867_, lean_object* v_declNameNonRec_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1865_, v_a_1866_, v___x_1867_, v_declNameNonRec_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
if (lean_obj_tag(v_a_1875_) == 0)
{
lean_object* v___x_1877_; 
v___x_1877_ = l_List_reverse___redArg(v_a_1876_);
return v___x_1877_;
}
else
{
lean_object* v_head_1878_; lean_object* v_tail_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1888_; 
v_head_1878_ = lean_ctor_get(v_a_1875_, 0);
v_tail_1879_ = lean_ctor_get(v_a_1875_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_a_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1881_ = v_a_1875_;
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_tail_1879_);
lean_inc(v_head_1878_);
lean_dec(v_a_1875_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l_Lean_mkLevelParam(v_head_1878_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v_a_1876_);
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_a_1876_);
v___x_1885_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v_a_1875_ = v_tail_1879_;
v_a_1876_ = v___x_1885_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_levelParams_1889_, lean_object* v_declName_1890_, lean_object* v_declNameNonRec_1891_, lean_object* v_name_1892_, lean_object* v_xs_1893_, lean_object* v_body_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_us_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = lean_box(0);
lean_inc(v_levelParams_1889_);
v_us_1901_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1889_, v___x_1900_);
lean_inc(v_declName_1890_);
v___x_1902_ = l_Lean_mkConst(v_declName_1890_, v_us_1901_);
v___x_1903_ = l_Lean_mkAppN(v___x_1902_, v_xs_1893_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1904_ = l_Lean_Meta_mkEq(v___x_1903_, v_body_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = lean_box(0);
lean_inc(v_a_1905_);
v___f_1907_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1907_, 0, v_declName_1890_);
lean_closure_set(v___f_1907_, 1, v_a_1905_);
lean_closure_set(v___f_1907_, 2, v___x_1906_);
lean_closure_set(v___f_1907_, 3, v_declNameNonRec_1891_);
v___x_1908_ = 0;
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1909_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___f_1907_, v___x_1908_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; uint8_t v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
v___x_1911_ = 1;
v___x_1912_ = 1;
v___x_1913_ = l_Lean_Meta_mkForallFVars(v_xs_1893_, v_a_1905_, v___x_1908_, v___x_1911_, v___x_1911_, v___x_1912_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1915_ = l_Lean_Meta_letToHave(v_a_1914_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = l_Lean_Meta_mkLambdaFVars(v_xs_1893_, v_a_1910_, v___x_1908_, v___x_1911_, v___x_1908_, v___x_1911_, v___x_1912_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_a_1923_; lean_object* v___x_1924_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
lean_inc(v_name_1892_);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v_name_1892_);
lean_ctor_set(v___x_1919_, 1, v_levelParams_1889_);
lean_ctor_set(v___x_1919_, 2, v_a_1916_);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_name_1892_);
lean_ctor_set(v___x_1920_, 1, v___x_1900_);
v___x_1921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v_a_1918_);
lean_ctor_set(v___x_1921_, 2, v___x_1920_);
v___x_1922_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v___x_1921_, v___y_1898_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = l_Lean_addDecl(v_a_1923_, v___x_1908_, v___y_1897_, v___y_1898_);
return v___x_1924_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1916_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_name_1892_);
lean_dec(v_levelParams_1889_);
v_a_1925_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1917_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1917_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1910_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_name_1892_);
lean_dec(v_levelParams_1889_);
v_a_1933_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1915_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1915_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1910_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_name_1892_);
lean_dec(v_levelParams_1889_);
v_a_1941_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1913_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1913_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_a_1905_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_name_1892_);
lean_dec(v_levelParams_1889_);
v_a_1949_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1909_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1909_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_name_1892_);
lean_dec(v_declNameNonRec_1891_);
lean_dec(v_declName_1890_);
lean_dec(v_levelParams_1889_);
v_a_1957_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1904_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1904_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_levelParams_1965_, lean_object* v_declName_1966_, lean_object* v_declNameNonRec_1967_, lean_object* v_name_1968_, lean_object* v_xs_1969_, lean_object* v_body_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_levelParams_1965_, v_declName_1966_, v_declNameNonRec_1967_, v_name_1968_, v_xs_1969_, v_body_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec_ref(v_xs_1969_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1977_, lean_object* v_info_1978_, lean_object* v_name_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v_levelParams_1986_; lean_object* v_value_1987_; lean_object* v_declNameNonRec_1988_; lean_object* v_fileName_1989_; lean_object* v_fileMap_1990_; lean_object* v_options_1991_; lean_object* v_currRecDepth_1992_; lean_object* v_ref_1993_; lean_object* v_currNamespace_1994_; lean_object* v_openDecls_1995_; lean_object* v_initHeartbeats_1996_; lean_object* v_maxHeartbeats_1997_; lean_object* v_quotContext_1998_; lean_object* v_currMacroScope_1999_; lean_object* v_cancelTk_x3f_2000_; uint8_t v_suppressElabErrors_2001_; lean_object* v_inheritedTraceOptions_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2057_; 
v___x_1985_ = lean_st_ref_get(v_a_1983_);
v_levelParams_1986_ = lean_ctor_get(v_info_1978_, 1);
lean_inc(v_levelParams_1986_);
v_value_1987_ = lean_ctor_get(v_info_1978_, 3);
lean_inc_ref(v_value_1987_);
v_declNameNonRec_1988_ = lean_ctor_get(v_info_1978_, 5);
lean_inc(v_declNameNonRec_1988_);
lean_dec_ref(v_info_1978_);
v_fileName_1989_ = lean_ctor_get(v_a_1982_, 0);
v_fileMap_1990_ = lean_ctor_get(v_a_1982_, 1);
v_options_1991_ = lean_ctor_get(v_a_1982_, 2);
v_currRecDepth_1992_ = lean_ctor_get(v_a_1982_, 3);
v_ref_1993_ = lean_ctor_get(v_a_1982_, 5);
v_currNamespace_1994_ = lean_ctor_get(v_a_1982_, 6);
v_openDecls_1995_ = lean_ctor_get(v_a_1982_, 7);
v_initHeartbeats_1996_ = lean_ctor_get(v_a_1982_, 8);
v_maxHeartbeats_1997_ = lean_ctor_get(v_a_1982_, 9);
v_quotContext_1998_ = lean_ctor_get(v_a_1982_, 10);
v_currMacroScope_1999_ = lean_ctor_get(v_a_1982_, 11);
v_cancelTk_x3f_2000_ = lean_ctor_get(v_a_1982_, 12);
v_suppressElabErrors_2001_ = lean_ctor_get_uint8(v_a_1982_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2002_ = lean_ctor_get(v_a_1982_, 13);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_a_1982_, 4);
lean_dec(v_unused_2058_);
v___x_2004_ = v_a_1982_;
v_isShared_2005_ = v_isSharedCheck_2057_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_inheritedTraceOptions_2002_);
lean_inc(v_cancelTk_x3f_2000_);
lean_inc(v_currMacroScope_1999_);
lean_inc(v_quotContext_1998_);
lean_inc(v_maxHeartbeats_1997_);
lean_inc(v_initHeartbeats_1996_);
lean_inc(v_openDecls_1995_);
lean_inc(v_currNamespace_1994_);
lean_inc(v_ref_1993_);
lean_inc(v_currRecDepth_1992_);
lean_inc(v_options_1991_);
lean_inc(v_fileMap_1990_);
lean_inc(v_fileName_1989_);
lean_dec(v_a_1982_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2057_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_env_2006_; lean_object* v___f_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v_fileName_2014_; lean_object* v_fileMap_2015_; lean_object* v_currRecDepth_2016_; lean_object* v_ref_2017_; lean_object* v_currNamespace_2018_; lean_object* v_openDecls_2019_; lean_object* v_initHeartbeats_2020_; lean_object* v_maxHeartbeats_2021_; lean_object* v_quotContext_2022_; lean_object* v_currMacroScope_2023_; lean_object* v_cancelTk_x3f_2024_; uint8_t v_suppressElabErrors_2025_; lean_object* v_inheritedTraceOptions_2026_; lean_object* v___y_2027_; uint8_t v___y_2035_; uint8_t v___x_2056_; 
v_env_2006_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_ref(v_env_2006_);
lean_dec(v___x_1985_);
v___f_2007_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 11, 4);
lean_closure_set(v___f_2007_, 0, v_levelParams_1986_);
lean_closure_set(v___f_2007_, 1, v_declName_1977_);
lean_closure_set(v___f_2007_, 2, v_declNameNonRec_1988_);
lean_closure_set(v___f_2007_, 3, v_name_1979_);
v___x_2008_ = 0;
v___x_2009_ = l_Lean_Meta_tactic_hygienic;
v___x_2010_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_options_1991_, v___x_2009_, v___x_2008_);
v___x_2011_ = l_Lean_diagnostics;
v___x_2012_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_2010_, v___x_2011_);
v___x_2056_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2006_);
lean_dec_ref(v_env_2006_);
if (v___x_2056_ == 0)
{
if (v___x_2012_ == 0)
{
v_fileName_2014_ = v_fileName_1989_;
v_fileMap_2015_ = v_fileMap_1990_;
v_currRecDepth_2016_ = v_currRecDepth_1992_;
v_ref_2017_ = v_ref_1993_;
v_currNamespace_2018_ = v_currNamespace_1994_;
v_openDecls_2019_ = v_openDecls_1995_;
v_initHeartbeats_2020_ = v_initHeartbeats_1996_;
v_maxHeartbeats_2021_ = v_maxHeartbeats_1997_;
v_quotContext_2022_ = v_quotContext_1998_;
v_currMacroScope_2023_ = v_currMacroScope_1999_;
v_cancelTk_x3f_2024_ = v_cancelTk_x3f_2000_;
v_suppressElabErrors_2025_ = v_suppressElabErrors_2001_;
v_inheritedTraceOptions_2026_ = v_inheritedTraceOptions_2002_;
v___y_2027_ = v_a_1983_;
goto v___jp_2013_;
}
else
{
v___y_2035_ = v___x_2056_;
goto v___jp_2034_;
}
}
else
{
v___y_2035_ = v___x_2012_;
goto v___jp_2034_;
}
v___jp_2013_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2028_ = l_Lean_maxRecDepth;
v___x_2029_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v___x_2010_, v___x_2028_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 13, v_inheritedTraceOptions_2026_);
lean_ctor_set(v___x_2004_, 12, v_cancelTk_x3f_2024_);
lean_ctor_set(v___x_2004_, 11, v_currMacroScope_2023_);
lean_ctor_set(v___x_2004_, 10, v_quotContext_2022_);
lean_ctor_set(v___x_2004_, 9, v_maxHeartbeats_2021_);
lean_ctor_set(v___x_2004_, 8, v_initHeartbeats_2020_);
lean_ctor_set(v___x_2004_, 7, v_openDecls_2019_);
lean_ctor_set(v___x_2004_, 6, v_currNamespace_2018_);
lean_ctor_set(v___x_2004_, 5, v_ref_2017_);
lean_ctor_set(v___x_2004_, 4, v___x_2029_);
lean_ctor_set(v___x_2004_, 3, v_currRecDepth_2016_);
lean_ctor_set(v___x_2004_, 2, v___x_2010_);
lean_ctor_set(v___x_2004_, 1, v_fileMap_2015_);
lean_ctor_set(v___x_2004_, 0, v_fileName_2014_);
v___x_2031_ = v___x_2004_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fileName_2014_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_fileMap_2015_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_currRecDepth_2016_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2033_, 5, v_ref_2017_);
lean_ctor_set(v_reuseFailAlloc_2033_, 6, v_currNamespace_2018_);
lean_ctor_set(v_reuseFailAlloc_2033_, 7, v_openDecls_2019_);
lean_ctor_set(v_reuseFailAlloc_2033_, 8, v_initHeartbeats_2020_);
lean_ctor_set(v_reuseFailAlloc_2033_, 9, v_maxHeartbeats_2021_);
lean_ctor_set(v_reuseFailAlloc_2033_, 10, v_quotContext_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 11, v_currMacroScope_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 12, v_cancelTk_x3f_2024_);
lean_ctor_set(v_reuseFailAlloc_2033_, 13, v_inheritedTraceOptions_2026_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; 
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*14, v___x_2012_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*14 + 1, v_suppressElabErrors_2025_);
v___x_2032_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__9___redArg(v_value_1987_, v___f_2007_, v___x_2008_, v_a_1980_, v_a_1981_, v___x_2031_, v___y_2027_);
return v___x_2032_;
}
}
v___jp_2034_:
{
if (v___y_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v_env_2037_; lean_object* v_nextMacroScope_2038_; lean_object* v_ngen_2039_; lean_object* v_auxDeclNGen_2040_; lean_object* v_traceState_2041_; lean_object* v_messages_2042_; lean_object* v_infoState_2043_; lean_object* v_snapshotTasks_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2054_; 
v___x_2036_ = lean_st_ref_take(v_a_1983_);
v_env_2037_ = lean_ctor_get(v___x_2036_, 0);
v_nextMacroScope_2038_ = lean_ctor_get(v___x_2036_, 1);
v_ngen_2039_ = lean_ctor_get(v___x_2036_, 2);
v_auxDeclNGen_2040_ = lean_ctor_get(v___x_2036_, 3);
v_traceState_2041_ = lean_ctor_get(v___x_2036_, 4);
v_messages_2042_ = lean_ctor_get(v___x_2036_, 6);
v_infoState_2043_ = lean_ctor_get(v___x_2036_, 7);
v_snapshotTasks_2044_ = lean_ctor_get(v___x_2036_, 8);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2036_, 5);
lean_dec(v_unused_2055_);
v___x_2046_ = v___x_2036_;
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_snapshotTasks_2044_);
lean_inc(v_infoState_2043_);
lean_inc(v_messages_2042_);
lean_inc(v_traceState_2041_);
lean_inc(v_auxDeclNGen_2040_);
lean_inc(v_ngen_2039_);
lean_inc(v_nextMacroScope_2038_);
lean_inc(v_env_2037_);
lean_dec(v___x_2036_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2048_ = l_Lean_Kernel_enableDiag(v_env_2037_, v___x_2012_);
v___x_2049_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 5, v___x_2049_);
lean_ctor_set(v___x_2046_, 0, v___x_2048_);
v___x_2051_ = v___x_2046_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_nextMacroScope_2038_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_ngen_2039_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_auxDeclNGen_2040_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_traceState_2041_);
lean_ctor_set(v_reuseFailAlloc_2053_, 5, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 6, v_messages_2042_);
lean_ctor_set(v_reuseFailAlloc_2053_, 7, v_infoState_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 8, v_snapshotTasks_2044_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_st_ref_set(v_a_1983_, v___x_2051_);
v_fileName_2014_ = v_fileName_1989_;
v_fileMap_2015_ = v_fileMap_1990_;
v_currRecDepth_2016_ = v_currRecDepth_1992_;
v_ref_2017_ = v_ref_1993_;
v_currNamespace_2018_ = v_currNamespace_1994_;
v_openDecls_2019_ = v_openDecls_1995_;
v_initHeartbeats_2020_ = v_initHeartbeats_1996_;
v_maxHeartbeats_2021_ = v_maxHeartbeats_1997_;
v_quotContext_2022_ = v_quotContext_1998_;
v_currMacroScope_2023_ = v_currMacroScope_1999_;
v_cancelTk_x3f_2024_ = v_cancelTk_x3f_2000_;
v_suppressElabErrors_2025_ = v_suppressElabErrors_2001_;
v_inheritedTraceOptions_2026_ = v_inheritedTraceOptions_2002_;
v___y_2027_ = v_a_1983_;
goto v___jp_2013_;
}
}
}
else
{
v_fileName_2014_ = v_fileName_1989_;
v_fileMap_2015_ = v_fileMap_1990_;
v_currRecDepth_2016_ = v_currRecDepth_1992_;
v_ref_2017_ = v_ref_1993_;
v_currNamespace_2018_ = v_currNamespace_1994_;
v_openDecls_2019_ = v_openDecls_1995_;
v_initHeartbeats_2020_ = v_initHeartbeats_1996_;
v_maxHeartbeats_2021_ = v_maxHeartbeats_1997_;
v_quotContext_2022_ = v_quotContext_1998_;
v_currMacroScope_2023_ = v_currMacroScope_1999_;
v_cancelTk_x3f_2024_ = v_cancelTk_x3f_2000_;
v_suppressElabErrors_2025_ = v_suppressElabErrors_2001_;
v_inheritedTraceOptions_2026_ = v_inheritedTraceOptions_2002_;
v___y_2027_ = v_a_1983_;
goto v___jp_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2059_, lean_object* v_info_2060_, lean_object* v_name_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2059_, v_info_2060_, v_name_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2068_, lean_object* v_info_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v_env_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = lean_st_ref_get(v_a_2073_);
v_env_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_ref(v_env_2076_);
lean_dec(v___x_2075_);
v___x_2077_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2068_);
v___x_2078_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2076_, v_declName_2068_, v___x_2077_);
lean_inc(v___x_2078_);
lean_inc(v_declName_2068_);
v___x_2079_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2079_, 0, v_declName_2068_);
lean_closure_set(v___x_2079_, 1, v_info_2069_);
lean_closure_set(v___x_2079_, 2, v___x_2078_);
lean_inc(v___x_2078_);
v___x_2080_ = l_Lean_Meta_realizeConst(v_declName_2068_, v___x_2078_, v___x_2079_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2088_);
v___x_2082_ = v___x_2080_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v___x_2080_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2078_);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2078_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v___x_2078_);
v_a_2089_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2080_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2097_, lean_object* v_info_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2097_, v_info_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_env_2113_; lean_object* v_env_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2111_ = lean_st_ref_get(v_a_2109_);
v___x_2112_ = lean_st_ref_get(v_a_2109_);
v_env_2113_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2113_);
lean_dec(v___x_2111_);
v_env_2114_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_ref(v_env_2114_);
lean_dec(v___x_2112_);
v___x_2115_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2105_);
v___x_2116_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2113_, v_declName_2105_, v___x_2115_);
v___x_2117_ = 1;
lean_inc(v___x_2116_);
lean_inc_ref(v_env_2114_);
v___x_2118_ = l_Lean_Environment_contains(v_env_2114_, v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v_toEnvExtension_2120_; lean_object* v_asyncMode_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
lean_dec(v___x_2116_);
v___x_2119_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_ref(v_toEnvExtension_2120_);
v_asyncMode_2121_ = lean_ctor_get(v_toEnvExtension_2120_, 2);
lean_inc(v_asyncMode_2121_);
lean_dec_ref(v_toEnvExtension_2120_);
v___x_2122_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2123_ = 0;
lean_inc(v_declName_2105_);
v___x_2124_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2122_, v___x_2119_, v_env_2114_, v_declName_2105_, v_asyncMode_2121_, v___x_2123_);
lean_dec(v_asyncMode_2121_);
if (lean_obj_tag(v___x_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2149_; 
v_val_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2149_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_val_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2149_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2105_, v_val_2125_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2140_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v_a_2130_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
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
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_2127_);
v_a_2141_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2129_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2129_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec(v___x_2124_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_declName_2105_);
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v_env_2114_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_declName_2105_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2116_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2164_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2166_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
res = l_Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1270222229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
}
#ifdef __cplusplus
}
#endif
