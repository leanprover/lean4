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
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 126, 228, 214, 96, 108, 195, 201)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 154, 190, 235, 71, 53, 215, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 113, 187, 250, 69, 106, 19, 81)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "mkUnfoldEq rfl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkUnfoldEq after rwFixEq:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkUnfoldEq after deltaLHS:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to generate unfold theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkUnfoldEq start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_17_, lean_object* v_n_18_, lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Lean_Environment_hasExposedBody(v_env_17_, v_n_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_env_21_, lean_object* v_n_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(v_env_21_, v_n_22_, v_x_23_);
lean_dec_ref(v_x_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_26_, lean_object* v_x_27_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v_k_28_; lean_object* v_v_29_; lean_object* v_l_30_; lean_object* v_r_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_k_28_ = lean_ctor_get(v_x_27_, 1);
v_v_29_ = lean_ctor_get(v_x_27_, 2);
v_l_30_ = lean_ctor_get(v_x_27_, 3);
v_r_31_ = lean_ctor_get(v_x_27_, 4);
v___x_32_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_26_, v_l_30_);
lean_inc(v_v_29_);
lean_inc(v_k_28_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v_k_28_);
lean_ctor_set(v___x_33_, 1, v_v_29_);
v___x_34_ = lean_array_push(v___x_32_, v___x_33_);
v_init_26_ = v___x_34_;
v_x_27_ = v_r_31_;
goto _start;
}
else
{
return v_init_26_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_36_, v_x_37_);
lean_dec(v_x_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_41_, lean_object* v_s_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v_all_45_; lean_object* v___x_46_; lean_object* v_exported_47_; lean_object* v___x_48_; 
v___f_43_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_43_, 0, v_env_41_);
v___x_44_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_));
v_all_45_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_44_, v_s_42_);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_43_, v_s_42_);
v_exported_47_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_44_, v___x_46_);
lean_dec(v___x_46_);
lean_inc_ref(v_exported_47_);
v___x_48_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_48_, 0, v_exported_47_);
lean_ctor_set(v___x_48_, 1, v_exported_47_);
lean_ctor_set(v___x_48_, 2, v_all_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___f_62_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_));
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_));
v___x_64_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_));
v___x_65_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_63_, v___x_64_, v___f_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object* v_init_68_, lean_object* v_t_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_68_, v_t_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_71_, lean_object* v_t_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2__spec__0(v_init_71_, v_t_72_);
lean_dec(v_t_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v_____do__lift_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_bool_not(v_____do__lift_74_);
v___x_81_ = lean_box(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v_____do__lift_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_____do__lift_3561__boxed_89_; lean_object* v_res_90_; 
v_____do__lift_3561__boxed_89_ = lean_unbox(v_____do__lift_83_);
v_res_90_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v_____do__lift_3561__boxed_89_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_eq(v_i_92_, v_stop_93_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v_type_101_; uint8_t v___x_102_; uint8_t v_a_104_; lean_object* v___x_110_; 
v___x_100_ = lean_array_uget_borrowed(v_as_91_, v_i_92_);
v_type_101_ = lean_ctor_get(v___x_100_, 6);
v___x_102_ = 1;
lean_inc_ref(v_type_101_);
v___x_110_ = l_Lean_Meta_isProp(v_type_101_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; uint8_t v___x_112_; uint8_t v___x_113_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = lean_unbox(v_a_111_);
lean_dec(v_a_111_);
v___x_113_ = lean_bool_not(v___x_112_);
v_a_104_ = v___x_113_;
goto v___jp_103_;
}
else
{
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_114_; uint8_t v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_110_, 1);
v___x_115_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
v_a_104_ = v___x_115_;
goto v___jp_103_;
}
else
{
return v___x_110_;
}
}
v___jp_103_:
{
if (v_a_104_ == 0)
{
size_t v___x_105_; size_t v___x_106_; 
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_add(v_i_92_, v___x_105_);
v_i_92_ = v___x_106_;
goto _start;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_box(v___x_102_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
}
else
{
uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = 0;
v___x_117_ = lean_box(v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_119_, lean_object* v_i_120_, lean_object* v_stop_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
size_t v_i_boxed_127_; size_t v_stop_boxed_128_; lean_object* v_res_129_; 
v_i_boxed_127_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_stop_boxed_128_ = lean_unbox_usize(v_stop_121_);
lean_dec(v_stop_121_);
v_res_129_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_119_, v_i_boxed_127_, v_stop_boxed_128_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec_ref(v_as_119_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_130_, lean_object* v_declNameNonRec_131_, lean_object* v_fixedParamPerms_132_, lean_object* v_fixpointType_133_, lean_object* v_as_134_, size_t v_i_135_, size_t v_stop_136_, lean_object* v_b_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_eq(v_i_135_, v_stop_136_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v_levelParams_140_; lean_object* v_declName_141_; lean_object* v_type_142_; lean_object* v_value_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; 
v___x_139_ = lean_array_uget_borrowed(v_as_134_, v_i_135_);
v_levelParams_140_ = lean_ctor_get(v___x_139_, 1);
v_declName_141_ = lean_ctor_get(v___x_139_, 3);
v_type_142_ = lean_ctor_get(v___x_139_, 6);
v_value_143_ = lean_ctor_get(v___x_139_, 7);
v___x_144_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc_ref(v_fixpointType_133_);
lean_inc_ref(v_fixedParamPerms_132_);
lean_inc(v_declNameNonRec_131_);
lean_inc_ref(v___x_130_);
lean_inc_ref(v_value_143_);
lean_inc_ref(v_type_142_);
lean_inc(v_levelParams_140_);
lean_inc_n(v_declName_141_, 2);
v___x_145_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_145_, 0, v_declName_141_);
lean_ctor_set(v___x_145_, 1, v_levelParams_140_);
lean_ctor_set(v___x_145_, 2, v_type_142_);
lean_ctor_set(v___x_145_, 3, v_value_143_);
lean_ctor_set(v___x_145_, 4, v___x_130_);
lean_ctor_set(v___x_145_, 5, v_declNameNonRec_131_);
lean_ctor_set(v___x_145_, 6, v_fixedParamPerms_132_);
lean_ctor_set(v___x_145_, 7, v_fixpointType_133_);
v___x_146_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_144_, v_b_137_, v_declName_141_, v___x_145_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_135_, v___x_147_);
v_i_135_ = v___x_148_;
v_b_137_ = v___x_146_;
goto _start;
}
else
{
lean_dec_ref(v_fixpointType_133_);
lean_dec_ref(v_fixedParamPerms_132_);
lean_dec(v_declNameNonRec_131_);
lean_dec_ref(v___x_130_);
return v_b_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_150_, lean_object* v_declNameNonRec_151_, lean_object* v_fixedParamPerms_152_, lean_object* v_fixpointType_153_, lean_object* v_as_154_, lean_object* v_i_155_, lean_object* v_stop_156_, lean_object* v_b_157_){
_start:
{
size_t v_i_boxed_158_; size_t v_stop_boxed_159_; lean_object* v_res_160_; 
v_i_boxed_158_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_stop_boxed_159_ = lean_unbox_usize(v_stop_156_);
lean_dec(v_stop_156_);
v_res_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_150_, v_declNameNonRec_151_, v_fixedParamPerms_152_, v_fixpointType_153_, v_as_154_, v_i_boxed_158_, v_stop_boxed_159_, v_b_157_);
lean_dec_ref(v_as_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_161_, size_t v_i_162_, lean_object* v_bs_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_164_ == 0)
{
return v_bs_163_;
}
else
{
lean_object* v_v_165_; lean_object* v_declName_166_; lean_object* v___x_167_; lean_object* v_bs_x27_168_; size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v_v_165_ = lean_array_uget_borrowed(v_bs_163_, v_i_162_);
v_declName_166_ = lean_ctor_get(v_v_165_, 3);
lean_inc(v_declName_166_);
v___x_167_ = lean_unsigned_to_nat(0u);
v_bs_x27_168_ = lean_array_uset(v_bs_163_, v_i_162_, v___x_167_);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_162_, v___x_169_);
v___x_171_ = lean_array_uset(v_bs_x27_168_, v_i_162_, v_declName_166_);
v_i_162_ = v___x_170_;
v_bs_163_ = v___x_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_173_, lean_object* v_i_174_, lean_object* v_bs_175_){
_start:
{
size_t v_sz_boxed_176_; size_t v_i_boxed_177_; lean_object* v_res_178_; 
v_sz_boxed_176_ = lean_unbox_usize(v_sz_173_);
lean_dec(v_sz_173_);
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_res_178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_176_, v_i_boxed_177_, v_bs_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_179_, size_t v_i_180_, size_t v_stop_181_, lean_object* v_b_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_usize_dec_eq(v_i_180_, v_stop_181_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v_declName_188_; lean_object* v___x_189_; 
v___x_187_ = lean_array_uget_borrowed(v_as_179_, v_i_180_);
v_declName_188_ = lean_ctor_get(v___x_187_, 3);
lean_inc(v_declName_188_);
v___x_189_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_188_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; size_t v___x_191_; size_t v___x_192_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_180_, v___x_191_);
v_i_180_ = v___x_192_;
v_b_182_ = v_a_190_;
goto _start;
}
else
{
return v___x_189_;
}
}
else
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v_b_182_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
size_t v_i_boxed_202_; size_t v_stop_boxed_203_; lean_object* v_res_204_; 
v_i_boxed_202_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_203_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_195_, v_i_boxed_202_, v_stop_boxed_203_, v_b_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_as_195_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(lean_object* v_as_205_, size_t v_i_206_, size_t v_stop_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_usize_dec_eq(v_i_206_, v_stop_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v_kind_210_; uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_209_ = lean_array_uget_borrowed(v_as_205_, v_i_206_);
v_kind_210_ = lean_ctor_get_uint8(v___x_209_, sizeof(void*)*9);
v___x_211_ = l_Lean_Elab_DefKind_isTheorem(v_kind_210_);
v___x_212_ = lean_bool_not(v___x_211_);
if (v___x_212_ == 0)
{
size_t v___x_213_; size_t v___x_214_; 
v___x_213_ = ((size_t)1ULL);
v___x_214_ = lean_usize_add(v_i_206_, v___x_213_);
v_i_206_ = v___x_214_;
goto _start;
}
else
{
return v___x_212_;
}
}
else
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v_as_217_, lean_object* v_i_218_, lean_object* v_stop_219_){
_start:
{
size_t v_i_boxed_220_; size_t v_stop_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_i_boxed_220_ = lean_unbox_usize(v_i_218_);
lean_dec(v_i_218_);
v_stop_boxed_221_ = lean_unbox_usize(v_stop_219_);
lean_dec(v_stop_219_);
v_res_222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v_as_217_, v_i_boxed_220_, v_stop_boxed_221_);
lean_dec_ref(v_as_217_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_230_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set(v___x_230_, 3, v___x_229_);
lean_ctor_set(v___x_230_, 4, v___x_229_);
lean_ctor_set(v___x_230_, 5, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_231_, lean_object* v_declNameNonRec_232_, lean_object* v_fixedParamPerms_233_, lean_object* v_fixpointType_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_nextMacroScope_241_; lean_object* v_ngen_242_; lean_object* v_auxDeclNGen_243_; lean_object* v_traceState_244_; lean_object* v_messages_245_; lean_object* v_infoState_246_; lean_object* v_snapshotTasks_247_; lean_object* v___y_248_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v_a_272_; lean_object* v___y_294_; uint8_t v___y_306_; lean_object* v___y_327_; uint8_t v___x_328_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v_preDefs_231_);
v___x_328_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_328_ == 0)
{
goto v___jp_318_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_nat_dec_le(v___x_270_, v___x_270_);
if (v___x_330_ == 0)
{
if (v___x_328_ == 0)
{
goto v___jp_318_;
}
else
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((size_t)0ULL);
v___x_332_ = lean_usize_of_nat(v___x_270_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_231_, v___x_331_, v___x_332_, v___x_329_, v_a_237_, v_a_238_);
v___y_327_ = v___x_333_;
goto v___jp_326_;
}
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_270_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_231_, v___x_334_, v___x_335_, v___x_329_, v_a_237_, v_a_238_);
v___y_327_ = v___x_336_;
goto v___jp_326_;
}
}
v___jp_240_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_mctx_253_; lean_object* v_zetaDeltaFVarIds_254_; lean_object* v_postponed_255_; lean_object* v_diag_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
v___x_250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_250_, 0, v___y_248_);
lean_ctor_set(v___x_250_, 1, v_nextMacroScope_241_);
lean_ctor_set(v___x_250_, 2, v_ngen_242_);
lean_ctor_set(v___x_250_, 3, v_auxDeclNGen_243_);
lean_ctor_set(v___x_250_, 4, v_traceState_244_);
lean_ctor_set(v___x_250_, 5, v___x_249_);
lean_ctor_set(v___x_250_, 6, v_messages_245_);
lean_ctor_set(v___x_250_, 7, v_infoState_246_);
lean_ctor_set(v___x_250_, 8, v_snapshotTasks_247_);
v___x_251_ = lean_st_ref_set(v_a_238_, v___x_250_);
v___x_252_ = lean_st_ref_take(v_a_236_);
v_mctx_253_ = lean_ctor_get(v___x_252_, 0);
v_zetaDeltaFVarIds_254_ = lean_ctor_get(v___x_252_, 2);
v_postponed_255_ = lean_ctor_get(v___x_252_, 3);
v_diag_256_ = lean_ctor_get(v___x_252_, 4);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_252_, 1);
lean_dec(v_unused_268_);
v___x_258_ = v___x_252_;
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_diag_256_);
lean_inc(v_postponed_255_);
lean_inc(v_zetaDeltaFVarIds_254_);
lean_inc(v_mctx_253_);
lean_dec(v___x_252_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_mctx_253_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_zetaDeltaFVarIds_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_postponed_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_diag_256_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_st_ref_set(v_a_236_, v___x_262_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
}
v___jp_271_:
{
if (v_a_272_ == 0)
{
lean_object* v___x_273_; lean_object* v_env_274_; lean_object* v_nextMacroScope_275_; lean_object* v_ngen_276_; lean_object* v_auxDeclNGen_277_; lean_object* v_traceState_278_; lean_object* v_messages_279_; lean_object* v_infoState_280_; lean_object* v_snapshotTasks_281_; uint8_t v___x_282_; 
v___x_273_ = lean_st_ref_take(v_a_238_);
v_env_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc_ref(v_env_274_);
v_nextMacroScope_275_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_nextMacroScope_275_);
v_ngen_276_ = lean_ctor_get(v___x_273_, 2);
lean_inc_ref(v_ngen_276_);
v_auxDeclNGen_277_ = lean_ctor_get(v___x_273_, 3);
lean_inc_ref(v_auxDeclNGen_277_);
v_traceState_278_ = lean_ctor_get(v___x_273_, 4);
lean_inc_ref(v_traceState_278_);
v_messages_279_ = lean_ctor_get(v___x_273_, 6);
lean_inc_ref(v_messages_279_);
v_infoState_280_ = lean_ctor_get(v___x_273_, 7);
lean_inc_ref(v_infoState_280_);
v_snapshotTasks_281_ = lean_ctor_get(v___x_273_, 8);
lean_inc_ref(v_snapshotTasks_281_);
lean_dec(v___x_273_);
v___x_282_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_282_ == 0)
{
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
v_nextMacroScope_241_ = v_nextMacroScope_275_;
v_ngen_242_ = v_ngen_276_;
v_auxDeclNGen_243_ = v_auxDeclNGen_277_;
v_traceState_244_ = v_traceState_278_;
v_messages_245_ = v_messages_279_;
v_infoState_246_ = v_infoState_280_;
v_snapshotTasks_247_ = v_snapshotTasks_281_;
v___y_248_ = v_env_274_;
goto v___jp_240_;
}
else
{
size_t v_sz_283_; size_t v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_sz_283_ = lean_array_size(v_preDefs_231_);
v___x_284_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_231_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_283_, v___x_284_, v_preDefs_231_);
v___x_286_ = lean_nat_dec_le(v___x_270_, v___x_270_);
if (v___x_286_ == 0)
{
if (v___x_282_ == 0)
{
lean_dec_ref(v___x_285_);
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
v_nextMacroScope_241_ = v_nextMacroScope_275_;
v_ngen_242_ = v_ngen_276_;
v_auxDeclNGen_243_ = v_auxDeclNGen_277_;
v_traceState_244_ = v_traceState_278_;
v_messages_245_ = v_messages_279_;
v_infoState_246_ = v_infoState_280_;
v_snapshotTasks_247_ = v_snapshotTasks_281_;
v___y_248_ = v_env_274_;
goto v___jp_240_;
}
else
{
size_t v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_usize_of_nat(v___x_270_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_285_, v_declNameNonRec_232_, v_fixedParamPerms_233_, v_fixpointType_234_, v_preDefs_231_, v___x_284_, v___x_287_, v_env_274_);
lean_dec_ref(v_preDefs_231_);
v_nextMacroScope_241_ = v_nextMacroScope_275_;
v_ngen_242_ = v_ngen_276_;
v_auxDeclNGen_243_ = v_auxDeclNGen_277_;
v_traceState_244_ = v_traceState_278_;
v_messages_245_ = v_messages_279_;
v_infoState_246_ = v_infoState_280_;
v_snapshotTasks_247_ = v_snapshotTasks_281_;
v___y_248_ = v___x_288_;
goto v___jp_240_;
}
}
else
{
size_t v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_usize_of_nat(v___x_270_);
v___x_290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_285_, v_declNameNonRec_232_, v_fixedParamPerms_233_, v_fixpointType_234_, v_preDefs_231_, v___x_284_, v___x_289_, v_env_274_);
lean_dec_ref(v_preDefs_231_);
v_nextMacroScope_241_ = v_nextMacroScope_275_;
v_ngen_242_ = v_ngen_276_;
v_auxDeclNGen_243_ = v_auxDeclNGen_277_;
v_traceState_244_ = v_traceState_278_;
v_messages_245_ = v_messages_279_;
v_infoState_246_ = v_infoState_280_;
v_snapshotTasks_247_ = v_snapshotTasks_281_;
v___y_248_ = v___x_290_;
goto v___jp_240_;
}
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
v___jp_293_:
{
if (lean_obj_tag(v___y_294_) == 0)
{
lean_object* v_a_295_; uint8_t v___x_296_; 
v_a_295_ = lean_ctor_get(v___y_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___y_294_, 1);
v___x_296_ = lean_unbox(v_a_295_);
lean_dec(v_a_295_);
v_a_272_ = v___x_296_;
goto v___jp_271_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
v_a_297_ = lean_ctor_get(v___y_294_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___y_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___y_294_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___y_294_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
uint8_t v___x_307_; 
v___x_307_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___y_306_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
v___y_294_ = v___x_308_;
goto v___jp_293_;
}
else
{
if (v___x_307_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = lean_bool_not(v___y_306_);
v_a_272_ = v___x_309_;
goto v___jp_271_;
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((size_t)0ULL);
v___x_311_ = lean_usize_of_nat(v___x_270_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_231_, v___x_310_, v___x_311_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; uint8_t v___x_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = lean_unbox(v_a_313_);
lean_dec(v_a_313_);
v___x_315_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_314_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
v___y_294_ = v___x_315_;
goto v___jp_293_;
}
else
{
v___y_294_ = v___x_312_;
goto v___jp_293_;
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
v___jp_318_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = lean_bool_not(v___x_319_);
v___y_306_ = v___x_320_;
goto v___jp_305_;
}
else
{
if (v___x_319_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = lean_bool_not(v___x_319_);
v___y_306_ = v___x_321_;
goto v___jp_305_;
}
else
{
size_t v___x_322_; size_t v___x_323_; uint8_t v___x_324_; uint8_t v___x_325_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_270_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v_preDefs_231_, v___x_322_, v___x_323_);
v___x_325_ = lean_bool_not(v___x_324_);
v___y_306_ = v___x_325_;
goto v___jp_305_;
}
}
}
v___jp_326_:
{
if (lean_obj_tag(v___y_327_) == 0)
{
lean_dec_ref_known(v___y_327_, 1);
goto v___jp_318_;
}
else
{
lean_dec_ref(v_fixpointType_234_);
lean_dec_ref(v_fixedParamPerms_233_);
lean_dec(v_declNameNonRec_232_);
lean_dec_ref(v_preDefs_231_);
return v___y_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_337_, lean_object* v_declNameNonRec_338_, lean_object* v_fixedParamPerms_339_, lean_object* v_fixpointType_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_337_, v_declNameNonRec_338_, v_fixedParamPerms_339_, v_fixpointType_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_347_, size_t v_i_348_, size_t v_stop_349_, lean_object* v_b_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_347_, v_i_348_, v_stop_349_, v_b_350_, v___y_353_, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_357_, lean_object* v_i_358_, lean_object* v_stop_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
size_t v_i_boxed_366_; size_t v_stop_boxed_367_; lean_object* v_res_368_; 
v_i_boxed_366_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_stop_boxed_367_ = lean_unbox_usize(v_stop_359_);
lean_dec(v_stop_359_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_357_, v_i_boxed_366_, v_stop_boxed_367_, v_b_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_as_357_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_369_, lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_369_, v_x_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_393_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_mvarId_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_410_, v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_419_, lean_object* v_declNameNonRec_420_, lean_object* v_n_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_name_eq(v_n_421_, v_declName_419_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_name_eq(v_n_421_, v_declNameNonRec_420_);
return v___x_423_;
}
else
{
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_424_, lean_object* v_declNameNonRec_425_, lean_object* v_n_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_424_, v_declNameNonRec_425_, v_n_426_);
lean_dec(v_n_426_);
lean_dec(v_declNameNonRec_425_);
lean_dec(v_declName_424_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_439_ = l_Lean_MessageData_ofFormat(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_442_, lean_object* v___f_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
lean_inc(v_mvarId_442_);
v___x_449_ = l_Lean_MVarId_getType_x27(v_mvarId_442_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = l_Lean_Expr_isAppOfArity(v_a_450_, v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_a_450_);
lean_dec_ref(v___f_443_);
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_455_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_456_ = l_Lean_Meta_throwTacticEx___redArg(v___x_454_, v_mvarId_442_, v___x_455_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_457_ = l_Lean_Expr_appFn_x21(v_a_450_);
v___x_458_ = l_Lean_Expr_appArg_x21(v___x_457_);
lean_dec_ref(v___x_457_);
v___x_459_ = 0;
v___x_460_ = l_Lean_Meta_deltaExpand(v___x_458_, v___f_443_, v___x_459_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_Expr_appArg_x21(v_a_450_);
lean_dec(v_a_450_);
v___x_463_ = l_Lean_Meta_mkEq(v_a_461_, v___x_462_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_442_, v_a_464_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_465_;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_mvarId_442_);
v_a_466_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_463_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_a_450_);
lean_dec(v_mvarId_442_);
v_a_474_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_460_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_460_);
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
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v___f_443_);
lean_dec(v_mvarId_442_);
v_a_482_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_449_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_449_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_490_, lean_object* v___f_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_490_, v___f_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_498_, lean_object* v_declNameNonRec_499_, lean_object* v_mvarId_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
v___f_506_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_506_, 0, v_declName_498_);
lean_closure_set(v___f_506_, 1, v_declNameNonRec_499_);
lean_inc(v_mvarId_500_);
v___f_507_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_507_, 0, v_mvarId_500_);
lean_closure_set(v___f_507_, 1, v___f_506_);
v___x_508_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_500_, v___f_507_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_509_, lean_object* v_declNameNonRec_510_, lean_object* v_mvarId_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_509_, v_declNameNonRec_510_, v_mvarId_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object* v_msg_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = l_Lean_instInhabitedExpr;
v___x_520_ = lean_panic_fn_borrowed(v___x_519_, v_msg_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_env_528_; lean_object* v___x_529_; lean_object* v_mctx_530_; lean_object* v_lctx_531_; lean_object* v_options_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_527_ = lean_st_ref_get(v___y_525_);
v_env_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_528_);
lean_dec(v___x_527_);
v___x_529_ = lean_st_ref_get(v___y_523_);
v_mctx_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_mctx_530_);
lean_dec(v___x_529_);
v_lctx_531_ = lean_ctor_get(v___y_522_, 2);
v_options_532_ = lean_ctor_get(v___y_524_, 2);
lean_inc_ref(v_options_532_);
lean_inc_ref(v_lctx_531_);
v___x_533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_533_, 0, v_env_528_);
lean_ctor_set(v___x_533_, 1, v_mctx_530_);
lean_ctor_set(v___x_533_, 2, v_lctx_531_);
lean_ctor_set(v___x_533_, 3, v_options_532_);
v___x_534_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_msgData_521_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_ref_549_; lean_object* v___x_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_ref_549_ = lean_ctor_get(v___y_546_, 5);
v___x_550_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_559_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_inc(v_ref_549_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_ref_549_);
lean_ctor_set(v___x_555_, 1, v_a_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 1);
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l_Lean_Expr_bvar___override(v___x_587_);
return v___x_588_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12(void){
_start:
{
lean_object* v___x_589_; size_t v___x_590_; 
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_590_ = lean_ptr_addr(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15));
v___x_595_ = lean_unsigned_to_nat(18u);
v___x_596_ = lean_unsigned_to_nat(1896u);
v___x_597_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14));
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_599_ = l_mkPanicMessageWithDecl(v___x_598_, v___x_597_, v___x_596_, v___x_595_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21(void){
_start:
{
lean_object* v___x_608_; lean_object* v_dummy_609_; 
v___x_608_ = lean_box(0);
v_dummy_609_ = l_Lean_Expr_sort___override(v___x_608_);
return v_dummy_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2));
v___x_622_ = lean_unsigned_to_nat(4u);
v___x_623_ = l_Lean_Expr_isAppOfArity(v_lhs_615_, v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4));
v___x_625_ = l_Lean_Expr_isAppOfArity(v_lhs_615_, v___x_624_, v___x_622_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Expr_isApp(v_lhs_615_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Expr_isProj(v_lhs_615_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_629_ = l_Lean_MessageData_ofExpr(v_lhs_615_);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_630_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = l_Lean_Expr_projExpr_x21(v_lhs_615_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
lean_inc_ref(v_a_616_);
lean_inc_ref(v___x_632_);
v___x_633_ = lean_infer_type(v___x_632_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_632_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___y_640_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_638_ = 0;
if (lean_obj_tag(v_lhs_615_) == 11)
{
lean_object* v_typeName_648_; lean_object* v_idx_649_; lean_object* v_struct_650_; lean_object* v___x_651_; size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v_typeName_648_ = lean_ctor_get(v_lhs_615_, 0);
v_idx_649_ = lean_ctor_get(v_lhs_615_, 1);
v_struct_650_ = lean_ctor_get(v_lhs_615_, 2);
v___x_651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_652_ = lean_ptr_addr(v_struct_650_);
v___x_653_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_inc(v_idx_649_);
lean_inc(v_typeName_648_);
lean_dec_ref_known(v_lhs_615_, 3);
v___x_655_ = l_Lean_Expr_proj___override(v_typeName_648_, v_idx_649_, v___x_651_);
v___y_640_ = v___x_655_;
goto v___jp_639_;
}
else
{
v___y_640_ = v_lhs_615_;
goto v___jp_639_;
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v_lhs_615_);
v___x_656_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
v___x_657_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_656_);
v___y_640_ = v___x_657_;
goto v___jp_639_;
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_641_ = l_Lean_mkLambda(v___x_637_, v___x_638_, v_a_634_, v___y_640_);
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_643_ = lean_unsigned_to_nat(2u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_array_push(v___x_644_, v___x_641_);
v___x_646_ = lean_array_push(v___x_645_, v_a_636_);
v___x_647_ = l_Lean_Meta_mkAppM(v___x_642_, v___x_646_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_647_;
}
}
else
{
lean_dec(v_a_634_);
lean_dec_ref(v_lhs_615_);
return v___x_635_;
}
}
else
{
lean_dec_ref(v___x_632_);
lean_dec_ref(v_lhs_615_);
return v___x_633_;
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_Lean_Expr_appFn_x21(v_lhs_615_);
v___x_659_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_658_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18));
v___x_662_ = l_Lean_Expr_appArg_x21(v_lhs_615_);
lean_dec_ref(v_lhs_615_);
v___x_663_ = lean_unsigned_to_nat(2u);
v___x_664_ = lean_mk_empty_array_with_capacity(v___x_663_);
v___x_665_ = lean_array_push(v___x_664_, v_a_660_);
v___x_666_ = lean_array_push(v___x_665_, v___x_662_);
v___x_667_ = l_Lean_Meta_mkAppM(v___x_661_, v___x_666_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_667_;
}
else
{
lean_dec_ref(v_lhs_615_);
return v___x_659_;
}
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_dummy_672_; lean_object* v_nargs_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20));
v___x_669_ = l_Lean_Expr_getAppFn(v_lhs_615_);
v___x_670_ = l_Lean_Expr_constLevels_x21(v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = l_Lean_mkConst(v___x_668_, v___x_670_);
v_dummy_672_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_673_ = l_Lean_Expr_getAppNumArgs(v_lhs_615_);
lean_inc(v_nargs_673_);
v___x_674_ = lean_mk_array(v_nargs_673_, v_dummy_672_);
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_sub(v_nargs_673_, v___x_675_);
lean_dec(v_nargs_673_);
v___x_677_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_615_, v___x_674_, v___x_676_);
v___x_678_ = l_Lean_mkAppN(v___x_671_, v___x_677_);
lean_dec_ref(v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_dummy_684_; lean_object* v_nargs_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23));
v___x_681_ = l_Lean_Expr_getAppFn(v_lhs_615_);
v___x_682_ = l_Lean_Expr_constLevels_x21(v___x_681_);
lean_dec_ref(v___x_681_);
v___x_683_ = l_Lean_mkConst(v___x_680_, v___x_682_);
v_dummy_684_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_685_ = l_Lean_Expr_getAppNumArgs(v_lhs_615_);
lean_inc(v_nargs_685_);
v___x_686_ = lean_mk_array(v_nargs_685_, v_dummy_684_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v_nargs_685_, v___x_687_);
lean_dec(v_nargs_685_);
v___x_689_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_615_, v___x_686_, v___x_688_);
v___x_690_ = l_Lean_mkAppN(v___x_683_, v___x_689_);
lean_dec_ref(v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_00_u03b1_699_, lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object* v_00_u03b1_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_707_, v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___f_722_; lean_object* v___x_1534__overap_723_; lean_object* v___x_724_; 
v___f_722_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1534__overap_723_ = lean_panic_fn_borrowed(v___f_722_, v_msg_716_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
v___x_724_ = lean_apply_5(v___x_1534__overap_723_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, lean_box(0));
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_ks_736_; lean_object* v_vs_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_761_; 
v_ks_736_ = lean_ctor_get(v_x_732_, 0);
v_vs_737_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_761_ == 0)
{
v___x_739_ = v_x_732_;
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_vs_737_);
lean_inc(v_ks_736_);
lean_dec(v_x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_761_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_ks_736_);
v___x_742_ = lean_nat_dec_lt(v_x_733_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_x_733_);
v___x_743_ = lean_array_push(v_ks_736_, v_x_734_);
v___x_744_ = lean_array_push(v_vs_737_, v_x_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_744_);
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v_k_x27_748_; uint8_t v___x_749_; 
v_k_x27_748_ = lean_array_fget_borrowed(v_ks_736_, v_x_733_);
v___x_749_ = l_Lean_instBEqMVarId_beq(v_x_734_, v_k_x27_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_ks_736_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_vs_737_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_x_733_, v___x_752_);
lean_dec(v_x_733_);
v_x_732_ = v___x_751_;
v_x_733_ = v___x_753_;
goto _start;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = lean_array_fset(v_ks_736_, v_x_733_, v_x_734_);
v___x_757_ = lean_array_fset(v_vs_737_, v_x_733_, v_x_735_);
lean_dec(v_x_733_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_757_);
lean_ctor_set(v___x_739_, 0, v___x_756_);
v___x_759_ = v___x_739_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_762_, lean_object* v_k_763_, lean_object* v_v_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_762_, v___x_765_, v_k_763_, v_v_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_768_, size_t v_x_769_, size_t v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v_es_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_j_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_es_773_ = lean_ctor_get(v_x_768_, 0);
v___x_774_ = ((size_t)31ULL);
v___x_775_ = lean_usize_land(v_x_769_, v___x_774_);
v_j_776_ = lean_usize_to_nat(v___x_775_);
v___x_777_ = lean_array_get_size(v_es_773_);
v___x_778_ = lean_nat_dec_lt(v_j_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_j_776_);
lean_dec(v_x_772_);
lean_dec(v_x_771_);
return v_x_768_;
}
else
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_817_; 
lean_inc_ref(v_es_773_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_x_768_, 0);
lean_dec(v_unused_818_);
v___x_780_ = v_x_768_;
v_isShared_781_ = v_isSharedCheck_817_;
goto v_resetjp_779_;
}
else
{
lean_dec(v_x_768_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_817_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_v_782_; lean_object* v___x_783_; lean_object* v_xs_x27_784_; lean_object* v___y_786_; 
v_v_782_ = lean_array_fget(v_es_773_, v_j_776_);
v___x_783_ = lean_box(0);
v_xs_x27_784_ = lean_array_fset(v_es_773_, v_j_776_, v___x_783_);
switch(lean_obj_tag(v_v_782_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v_key_791_ = lean_ctor_get(v_v_782_, 0);
v_val_792_ = lean_ctor_get(v_v_782_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_802_ == 0)
{
v___x_794_ = v_v_782_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_inc(v_key_791_);
lean_dec(v_v_782_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
uint8_t v___x_796_; 
v___x_796_ = l_Lean_instBEqMVarId_beq(v_x_771_, v_key_791_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_794_);
v___x_797_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_791_, v_val_792_, v_x_771_, v_x_772_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_792_);
lean_dec(v_key_791_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_x_772_);
lean_ctor_set(v___x_794_, 0, v_x_771_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_x_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_x_772_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v___y_786_ = v___x_800_;
goto v___jp_785_;
}
}
}
}
case 1:
{
lean_object* v_node_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_node_803_ = lean_ctor_get(v_v_782_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_815_ == 0)
{
v___x_805_ = v_v_782_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_node_803_);
lean_dec(v_v_782_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_807_ = ((size_t)5ULL);
v___x_808_ = lean_usize_shift_right(v_x_769_, v___x_807_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_x_770_, v___x_809_);
v___x_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_803_, v___x_808_, v___x_810_, v_x_771_, v_x_772_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v___y_786_ = v___x_813_;
goto v___jp_785_;
}
}
}
default: 
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_x_771_);
lean_ctor_set(v___x_816_, 1, v_x_772_);
v___y_786_ = v___x_816_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_fset(v_xs_x27_784_, v_j_776_, v___y_786_);
lean_dec(v_j_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_787_);
v___x_789_ = v___x_780_;
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
else
{
lean_object* v_ks_819_; lean_object* v_vs_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_840_; 
v_ks_819_ = lean_ctor_get(v_x_768_, 0);
v_vs_820_ = lean_ctor_get(v_x_768_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_840_ == 0)
{
v___x_822_ = v_x_768_;
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_vs_820_);
lean_inc(v_ks_819_);
lean_dec(v_x_768_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_820_);
v___x_825_ = v_reuseFailAlloc_839_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v_newNode_826_; uint8_t v___y_828_; size_t v___x_834_; uint8_t v___x_835_; 
v_newNode_826_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_825_, v_x_771_, v_x_772_);
v___x_834_ = ((size_t)7ULL);
v___x_835_ = lean_usize_dec_le(v___x_834_, v_x_770_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_826_);
v___x_837_ = lean_unsigned_to_nat(4u);
v___x_838_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
else
{
v___y_828_ = v___x_835_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v_ks_829_; lean_object* v_vs_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ks_829_ = lean_ctor_get(v_newNode_826_, 0);
lean_inc_ref(v_ks_829_);
v_vs_830_ = lean_ctor_get(v_newNode_826_, 1);
lean_inc_ref(v_vs_830_);
lean_dec_ref(v_newNode_826_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_770_, v_ks_829_, v_vs_830_, v___x_831_, v___x_832_);
lean_dec_ref(v_vs_830_);
lean_dec_ref(v_ks_829_);
return v___x_833_;
}
else
{
return v_newNode_826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_get_size(v_keys_842_);
v___x_847_ = lean_nat_dec_lt(v_i_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_i_844_);
return v_entries_845_;
}
else
{
lean_object* v_k_848_; lean_object* v_v_849_; uint64_t v___x_850_; size_t v_h_851_; size_t v___x_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v_h_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_k_848_ = lean_array_fget_borrowed(v_keys_842_, v_i_844_);
v_v_849_ = lean_array_fget_borrowed(v_vals_843_, v_i_844_);
v___x_850_ = l_Lean_instHashableMVarId_hash(v_k_848_);
v_h_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_sub(v_depth_841_, v___x_854_);
v___x_856_ = lean_usize_mul(v___x_852_, v___x_855_);
v_h_857_ = lean_usize_shift_right(v_h_851_, v___x_856_);
v___x_858_ = lean_nat_add(v_i_844_, v___x_853_);
lean_dec(v_i_844_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
v___x_859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_845_, v_h_857_, v_depth_841_, v_k_848_, v_v_849_);
v_i_844_ = v___x_858_;
v_entries_845_ = v___x_859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_861_, lean_object* v_keys_862_, lean_object* v_vals_863_, lean_object* v_i_864_, lean_object* v_entries_865_){
_start:
{
size_t v_depth_boxed_866_; lean_object* v_res_867_; 
v_depth_boxed_866_ = lean_unbox_usize(v_depth_861_);
lean_dec(v_depth_861_);
v_res_867_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_866_, v_keys_862_, v_vals_863_, v_i_864_, v_entries_865_);
lean_dec_ref(v_vals_863_);
lean_dec_ref(v_keys_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
size_t v_x_2109__boxed_873_; size_t v_x_2110__boxed_874_; lean_object* v_res_875_; 
v_x_2109__boxed_873_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_x_2110__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_res_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_868_, v_x_2109__boxed_873_, v_x_2110__boxed_874_, v_x_871_, v_x_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
uint64_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v___x_879_ = l_Lean_instHashableMVarId_hash(v_x_877_);
v___x_880_ = lean_uint64_to_usize(v___x_879_);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_876_, v___x_880_, v___x_881_, v_x_877_, v_x_878_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_883_, lean_object* v_val_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_mctx_888_; lean_object* v_cache_889_; lean_object* v_zetaDeltaFVarIds_890_; lean_object* v_postponed_891_; lean_object* v_diag_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_920_; 
v___x_887_ = lean_st_ref_take(v___y_885_);
v_mctx_888_ = lean_ctor_get(v___x_887_, 0);
v_cache_889_ = lean_ctor_get(v___x_887_, 1);
v_zetaDeltaFVarIds_890_ = lean_ctor_get(v___x_887_, 2);
v_postponed_891_ = lean_ctor_get(v___x_887_, 3);
v_diag_892_ = lean_ctor_get(v___x_887_, 4);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_920_ == 0)
{
v___x_894_ = v___x_887_;
v_isShared_895_ = v_isSharedCheck_920_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_diag_892_);
lean_inc(v_postponed_891_);
lean_inc(v_zetaDeltaFVarIds_890_);
lean_inc(v_cache_889_);
lean_inc(v_mctx_888_);
lean_dec(v___x_887_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_920_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_depth_896_; lean_object* v_levelAssignDepth_897_; lean_object* v_lmvarCounter_898_; lean_object* v_mvarCounter_899_; lean_object* v_lDecls_900_; lean_object* v_decls_901_; lean_object* v_userNames_902_; lean_object* v_lAssignment_903_; lean_object* v_eAssignment_904_; lean_object* v_dAssignment_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_919_; 
v_depth_896_ = lean_ctor_get(v_mctx_888_, 0);
v_levelAssignDepth_897_ = lean_ctor_get(v_mctx_888_, 1);
v_lmvarCounter_898_ = lean_ctor_get(v_mctx_888_, 2);
v_mvarCounter_899_ = lean_ctor_get(v_mctx_888_, 3);
v_lDecls_900_ = lean_ctor_get(v_mctx_888_, 4);
v_decls_901_ = lean_ctor_get(v_mctx_888_, 5);
v_userNames_902_ = lean_ctor_get(v_mctx_888_, 6);
v_lAssignment_903_ = lean_ctor_get(v_mctx_888_, 7);
v_eAssignment_904_ = lean_ctor_get(v_mctx_888_, 8);
v_dAssignment_905_ = lean_ctor_get(v_mctx_888_, 9);
v_isSharedCheck_919_ = !lean_is_exclusive(v_mctx_888_);
if (v_isSharedCheck_919_ == 0)
{
v___x_907_ = v_mctx_888_;
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_dAssignment_905_);
lean_inc(v_eAssignment_904_);
lean_inc(v_lAssignment_903_);
lean_inc(v_userNames_902_);
lean_inc(v_decls_901_);
lean_inc(v_lDecls_900_);
lean_inc(v_mvarCounter_899_);
lean_inc(v_lmvarCounter_898_);
lean_inc(v_levelAssignDepth_897_);
lean_inc(v_depth_896_);
lean_dec(v_mctx_888_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_904_, v_mvarId_883_, v_val_884_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 8, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_depth_896_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_levelAssignDepth_897_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_lmvarCounter_898_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_mvarCounter_899_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_lDecls_900_);
lean_ctor_set(v_reuseFailAlloc_918_, 5, v_decls_901_);
lean_ctor_set(v_reuseFailAlloc_918_, 6, v_userNames_902_);
lean_ctor_set(v_reuseFailAlloc_918_, 7, v_lAssignment_903_);
lean_ctor_set(v_reuseFailAlloc_918_, 8, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 9, v_dAssignment_905_);
v___x_911_ = v_reuseFailAlloc_918_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_911_);
v___x_913_ = v___x_894_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_cache_889_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_zetaDeltaFVarIds_890_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_postponed_891_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_diag_892_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_st_ref_set(v___y_885_, v___x_913_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_921_, lean_object* v_val_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_921_, v_val_922_, v___y_923_);
lean_dec(v___y_923_);
return v_res_925_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_930_ = lean_unsigned_to_nat(41u);
v___x_931_ = lean_unsigned_to_nat(70u);
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_934_ = l_mkPanicMessageWithDecl(v___x_933_, v___x_932_, v___x_931_, v___x_930_, v___x_929_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_936_ = lean_unsigned_to_nat(51u);
v___x_937_ = lean_unsigned_to_nat(72u);
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_940_ = l_mkPanicMessageWithDecl(v___x_939_, v___x_938_, v___x_937_, v___x_936_, v___x_935_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
lean_inc(v_mvarId_941_);
v___x_947_ = l_Lean_MVarId_getType_x27(v_mvarId_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_950_ = lean_unsigned_to_nat(3u);
v___x_951_ = l_Lean_Expr_isAppOfArity(v_a_948_, v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_a_948_);
lean_dec(v_mvarId_941_);
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_953_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_952_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = l_Lean_Expr_appFn_x21(v_a_948_);
v___x_955_ = l_Lean_Expr_appArg_x21(v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_955_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_n(v_a_957_, 2);
lean_dec_ref_known(v___x_956_, 1);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
v___x_958_ = lean_infer_type(v_a_957_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; uint8_t v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_Lean_Expr_isAppOfArity(v_a_959_, v___x_949_, v___x_950_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v_a_959_);
lean_dec(v_a_957_);
lean_dec(v_a_948_);
lean_dec(v_mvarId_941_);
v___x_961_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_962_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_961_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = l_Lean_Expr_appArg_x21(v_a_948_);
lean_dec(v_a_948_);
v___x_964_ = l_Lean_Expr_appArg_x21(v_a_959_);
lean_dec(v_a_959_);
v___x_965_ = l_Lean_Meta_mkEq(v___x_964_, v___x_963_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_box(0);
v___x_968_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_966_, v___x_967_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc_n(v_a_969_, 2);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_Meta_mkEqTrans(v_a_957_, v_a_969_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v___y_942_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_941_, v_a_971_, v___y_943_);
lean_dec(v___y_943_);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_981_);
v___x_974_ = v___x_972_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_Expr_mvarId_x21(v_a_969_);
lean_dec(v_a_969_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_969_);
lean_dec(v___y_943_);
lean_dec(v_mvarId_941_);
v_a_982_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_970_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_970_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_957_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_mvarId_941_);
v_a_990_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_968_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_968_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_957_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_mvarId_941_);
v_a_998_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_965_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_965_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_957_);
lean_dec(v_a_948_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_mvarId_941_);
v_a_1006_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_958_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_958_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_948_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_mvarId_941_);
v_a_1014_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_956_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_956_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v_mvarId_941_);
v_a_1022_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_947_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_947_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; 
lean_inc(v_mvarId_1037_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1043_, 0, v_mvarId_1037_);
v___x_1044_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1037_, v___f_1043_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1052_, lean_object* v_val_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1052_, v_val_1053_, v___y_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1060_, lean_object* v_val_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1060_, v_val_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1069_, v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1073_, lean_object* v_x_1074_, size_t v_x_1075_, size_t v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1074_, v_x_1075_, v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
size_t v_x_2589__boxed_1086_; size_t v_x_2590__boxed_1087_; lean_object* v_res_1088_; 
v_x_2589__boxed_1086_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_x_2590__boxed_1087_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_res_1088_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1080_, v_x_1081_, v_x_2589__boxed_1086_, v_x_2590__boxed_1087_, v_x_1084_, v_x_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1089_, lean_object* v_n_1090_, lean_object* v_k_1091_, lean_object* v_v_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1090_, v_k_1091_, v_v_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1094_, size_t v_depth_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_heq_1098_, lean_object* v_i_1099_, lean_object* v_entries_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1095_, v_keys_1096_, v_vals_1097_, v_i_1099_, v_entries_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_depth_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_entries_1108_){
_start:
{
size_t v_depth_boxed_1109_; lean_object* v_res_1110_; 
v_depth_boxed_1109_ = lean_unbox_usize(v_depth_1103_);
lean_dec(v_depth_1103_);
v_res_1110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1102_, v_depth_boxed_1109_, v_keys_1104_, v_vals_1105_, v_heq_1106_, v_i_1107_, v_entries_1108_);
lean_dec_ref(v_vals_1105_);
lean_dec_ref(v_keys_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1112_, v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1117_, lean_object* v_opt_1118_){
_start:
{
lean_object* v_name_1119_; lean_object* v_defValue_1120_; lean_object* v_map_1121_; lean_object* v___x_1122_; 
v_name_1119_ = lean_ctor_get(v_opt_1118_, 0);
v_defValue_1120_ = lean_ctor_get(v_opt_1118_, 1);
v_map_1121_ = lean_ctor_get(v_opts_1117_, 0);
v___x_1122_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1121_, v_name_1119_);
if (lean_obj_tag(v___x_1122_) == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_unbox(v_defValue_1120_);
return v___x_1123_;
}
else
{
lean_object* v_val_1124_; 
v_val_1124_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1122_, 1);
if (lean_obj_tag(v_val_1124_) == 1)
{
uint8_t v_v_1125_; 
v_v_1125_ = lean_ctor_get_uint8(v_val_1124_, 0);
lean_dec_ref_known(v_val_1124_, 0);
return v_v_1125_;
}
else
{
uint8_t v___x_1126_; 
lean_dec(v_val_1124_);
v___x_1126_ = lean_unbox(v_defValue_1120_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1127_, lean_object* v_opt_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1127_, v_opt_1128_);
lean_dec_ref(v_opt_1128_);
lean_dec_ref(v_opts_1127_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1131_, lean_object* v_opt_1132_){
_start:
{
lean_object* v_name_1133_; lean_object* v_defValue_1134_; lean_object* v_map_1135_; lean_object* v___x_1136_; 
v_name_1133_ = lean_ctor_get(v_opt_1132_, 0);
v_defValue_1134_ = lean_ctor_get(v_opt_1132_, 1);
v_map_1135_ = lean_ctor_get(v_opts_1131_, 0);
v___x_1136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1135_, v_name_1133_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_inc(v_defValue_1134_);
return v_defValue_1134_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1136_, 1);
if (lean_obj_tag(v_val_1137_) == 3)
{
lean_object* v_v_1138_; 
v_v_1138_ = lean_ctor_get(v_val_1137_, 0);
lean_inc(v_v_1138_);
lean_dec_ref_known(v_val_1137_, 1);
return v_v_1138_;
}
else
{
lean_dec(v_val_1137_);
lean_inc(v_defValue_1134_);
return v_defValue_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1139_, lean_object* v_opt_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1139_, v_opt_1140_);
lean_dec_ref(v_opt_1140_);
lean_dec_ref(v_opts_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_e_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = l_Lean_Expr_hasMVar(v_e_1142_);
v___x_1146_ = lean_bool_not(v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v_mctx_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1152_; lean_object* v_cache_1153_; lean_object* v_zetaDeltaFVarIds_1154_; lean_object* v_postponed_1155_; lean_object* v_diag_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1165_; 
v___x_1147_ = lean_st_ref_get(v___y_1143_);
v_mctx_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_mctx_1148_);
lean_dec(v___x_1147_);
v___x_1149_ = l_Lean_instantiateMVarsCore(v_mctx_1148_, v_e_1142_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fst_1150_);
v_snd_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v___x_1149_);
v___x_1152_ = lean_st_ref_take(v___y_1143_);
v_cache_1153_ = lean_ctor_get(v___x_1152_, 1);
v_zetaDeltaFVarIds_1154_ = lean_ctor_get(v___x_1152_, 2);
v_postponed_1155_ = lean_ctor_get(v___x_1152_, 3);
v_diag_1156_ = lean_ctor_get(v___x_1152_, 4);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1152_, 0);
lean_dec(v_unused_1166_);
v___x_1158_ = v___x_1152_;
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_diag_1156_);
lean_inc(v_postponed_1155_);
lean_inc(v_zetaDeltaFVarIds_1154_);
lean_inc(v_cache_1153_);
lean_dec(v___x_1152_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v_snd_1151_);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_snd_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_cache_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_zetaDeltaFVarIds_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_postponed_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_diag_1156_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_set(v___y_1143_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_fst_1150_);
return v___x_1163_;
}
}
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_e_1142_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_e_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1168_, v___y_1169_);
lean_dec(v___y_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_e_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1172_, v___y_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_e_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_e_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(lean_object* v_k_1186_, uint8_t v_allowLevelAssignments_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1187_, v_k_1186_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_a_1202_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1193_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1193_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg___boxed(lean_object* v_k_1210_, lean_object* v_allowLevelAssignments_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1217_; lean_object* v_res_1218_; 
v_allowLevelAssignments_boxed_1217_ = lean_unbox(v_allowLevelAssignments_1211_);
v_res_1218_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1210_, v_allowLevelAssignments_boxed_1217_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object* v_00_u03b1_1219_, lean_object* v_k_1220_, uint8_t v_allowLevelAssignments_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1220_, v_allowLevelAssignments_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_k_1229_, lean_object* v_allowLevelAssignments_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1236_; lean_object* v_res_1237_; 
v_allowLevelAssignments_boxed_1236_ = lean_unbox(v_allowLevelAssignments_1230_);
v_res_1237_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_00_u03b1_1228_, v_k_1229_, v_allowLevelAssignments_boxed_1236_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object* v_thm_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_env_1242_; lean_object* v_toConstantVal_1243_; lean_object* v_value_1244_; lean_object* v_all_1245_; uint8_t v___y_1247_; lean_object* v_type_1255_; uint8_t v___x_1256_; 
v___x_1241_ = lean_st_ref_get(v___y_1239_);
v_env_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref_n(v_env_1242_, 2);
lean_dec(v___x_1241_);
v_toConstantVal_1243_ = lean_ctor_get(v_thm_1238_, 0);
v_value_1244_ = lean_ctor_get(v_thm_1238_, 1);
v_all_1245_ = lean_ctor_get(v_thm_1238_, 2);
v_type_1255_ = lean_ctor_get(v_toConstantVal_1243_, 2);
v___x_1256_ = l_Lean_Environment_hasUnsafe(v_env_1242_, v_type_1255_);
if (v___x_1256_ == 0)
{
uint8_t v___x_1257_; 
v___x_1257_ = l_Lean_Environment_hasUnsafe(v_env_1242_, v_value_1244_);
v___y_1247_ = v___x_1257_;
goto v___jp_1246_;
}
else
{
lean_dec_ref(v_env_1242_);
v___y_1247_ = v___x_1256_;
goto v___jp_1246_;
}
v___jp_1246_:
{
if (v___y_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_thm_1238_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_inc(v_all_1245_);
lean_inc_ref(v_value_1244_);
lean_inc_ref(v_toConstantVal_1243_);
lean_dec_ref(v_thm_1238_);
v___x_1250_ = lean_box(0);
v___x_1251_ = 0;
v___x_1252_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1252_, 0, v_toConstantVal_1243_);
lean_ctor_set(v___x_1252_, 1, v_value_1244_);
lean_ctor_set(v___x_1252_, 2, v___x_1250_);
lean_ctor_set(v___x_1252_, 3, v_all_1245_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object* v_thm_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1258_, v___y_1259_);
lean_dec(v___y_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object* v_thm_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1262_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object* v_thm_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_thm_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(lean_object* v_k_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
v___x_1284_ = lean_apply_7(v_k_1276_, v_b_1277_, v_c_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, lean_box(0));
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(lean_object* v_k_1285_, lean_object* v_b_1286_, lean_object* v_c_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(v_k_1285_, v_b_1286_, v_c_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object* v_e_1294_, lean_object* v_k_1295_, uint8_t v_cleanupAnnotations_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___f_1302_; uint8_t v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1302_, 0, v_k_1295_);
v___x_1303_ = 1;
v___x_1304_ = 0;
v___x_1305_ = lean_box(0);
v___x_1306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1294_, v___x_1303_, v___x_1304_, v___x_1303_, v___x_1304_, v___x_1305_, v___f_1302_, v_cleanupAnnotations_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object* v_e_1323_, lean_object* v_k_1324_, lean_object* v_cleanupAnnotations_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; lean_object* v_res_1332_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1325_);
v_res_1332_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1323_, v_k_1324_, v_cleanupAnnotations_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object* v_00_u03b1_1333_, lean_object* v_e_1334_, lean_object* v_k_1335_, uint8_t v_cleanupAnnotations_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1334_, v_k_1335_, v_cleanupAnnotations_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_e_1344_, lean_object* v_k_1345_, lean_object* v_cleanupAnnotations_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1352_; lean_object* v_res_1353_; 
v_cleanupAnnotations_boxed_1352_ = lean_unbox(v_cleanupAnnotations_1346_);
v_res_1353_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_00_u03b1_1343_, v_e_1344_, v_k_1345_, v_cleanupAnnotations_boxed_1352_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_options_1363_; uint8_t v_hasTrace_1364_; 
v_options_1363_ = lean_ctor_get(v___y_1360_, 2);
v_hasTrace_1364_ = lean_ctor_get_uint8(v_options_1363_, sizeof(void*)*1);
if (v_hasTrace_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v___x_1357_);
v___x_1365_ = lean_box(v_hasTrace_1364_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v_inheritedTraceOptions_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_inheritedTraceOptions_1367_ = lean_ctor_get(v___y_1360_, 13);
v___x_1368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1369_ = l_Lean_Name_append(v___x_1368_, v___x_1357_);
v___x_1370_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1367_, v_options_1363_, v___x_1369_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_box(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1379_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1380_; double v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_float_of_nat(v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object* v_cls_1385_, lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_ref_1392_; lean_object* v___x_1393_; lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1438_; 
v_ref_1392_ = lean_ctor_get(v___y_1389_, 5);
v___x_1393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1438_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1438_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v_traceState_1399_; lean_object* v_env_1400_; lean_object* v_nextMacroScope_1401_; lean_object* v_ngen_1402_; lean_object* v_auxDeclNGen_1403_; lean_object* v_cache_1404_; lean_object* v_messages_1405_; lean_object* v_infoState_1406_; lean_object* v_snapshotTasks_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1437_; 
v___x_1398_ = lean_st_ref_take(v___y_1390_);
v_traceState_1399_ = lean_ctor_get(v___x_1398_, 4);
v_env_1400_ = lean_ctor_get(v___x_1398_, 0);
v_nextMacroScope_1401_ = lean_ctor_get(v___x_1398_, 1);
v_ngen_1402_ = lean_ctor_get(v___x_1398_, 2);
v_auxDeclNGen_1403_ = lean_ctor_get(v___x_1398_, 3);
v_cache_1404_ = lean_ctor_get(v___x_1398_, 5);
v_messages_1405_ = lean_ctor_get(v___x_1398_, 6);
v_infoState_1406_ = lean_ctor_get(v___x_1398_, 7);
v_snapshotTasks_1407_ = lean_ctor_get(v___x_1398_, 8);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1409_ = v___x_1398_;
v_isShared_1410_ = v_isSharedCheck_1437_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snapshotTasks_1407_);
lean_inc(v_infoState_1406_);
lean_inc(v_messages_1405_);
lean_inc(v_cache_1404_);
lean_inc(v_traceState_1399_);
lean_inc(v_auxDeclNGen_1403_);
lean_inc(v_ngen_1402_);
lean_inc(v_nextMacroScope_1401_);
lean_inc(v_env_1400_);
lean_dec(v___x_1398_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1437_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint64_t v_tid_1411_; lean_object* v_traces_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1436_; 
v_tid_1411_ = lean_ctor_get_uint64(v_traceState_1399_, sizeof(void*)*1);
v_traces_1412_ = lean_ctor_get(v_traceState_1399_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_traceState_1399_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1414_ = v_traceState_1399_;
v_isShared_1415_ = v_isSharedCheck_1436_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_traces_1412_);
lean_dec(v_traceState_1399_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1436_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; double v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0);
v___x_1418_ = 0;
v___x_1419_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1));
v___x_1420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1420_, 0, v_cls_1385_);
lean_ctor_set(v___x_1420_, 1, v___x_1416_);
lean_ctor_set(v___x_1420_, 2, v___x_1419_);
lean_ctor_set_float(v___x_1420_, sizeof(void*)*3, v___x_1417_);
lean_ctor_set_float(v___x_1420_, sizeof(void*)*3 + 8, v___x_1417_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*3 + 16, v___x_1418_);
v___x_1421_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2));
v___x_1422_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v_a_1394_);
lean_ctor_set(v___x_1422_, 2, v___x_1421_);
lean_inc(v_ref_1392_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_ref_1392_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_PersistentArray_push___redArg(v_traces_1412_, v___x_1423_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1424_);
v___x_1426_ = v___x_1414_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1424_);
lean_ctor_set_uint64(v_reuseFailAlloc_1435_, sizeof(void*)*1, v_tid_1411_);
v___x_1426_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1426_);
v___x_1428_ = v___x_1409_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_env_1400_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_nextMacroScope_1401_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_ngen_1402_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_auxDeclNGen_1403_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1434_, 5, v_cache_1404_);
lean_ctor_set(v_reuseFailAlloc_1434_, 6, v_messages_1405_);
lean_ctor_set(v_reuseFailAlloc_1434_, 7, v_infoState_1406_);
lean_ctor_set(v_reuseFailAlloc_1434_, 8, v_snapshotTasks_1407_);
v___x_1428_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = lean_st_ref_set(v___y_1390_, v___x_1428_);
v___x_1430_ = lean_box(0);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1430_);
v___x_1432_ = v___x_1396_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_cls_1439_, v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_o_1447_, lean_object* v_k_1448_, uint8_t v_v_1449_){
_start:
{
lean_object* v_map_1450_; uint8_t v_hasTrace_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1465_; 
v_map_1450_ = lean_ctor_get(v_o_1447_, 0);
v_hasTrace_1451_ = lean_ctor_get_uint8(v_o_1447_, sizeof(void*)*1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_o_1447_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1453_ = v_o_1447_;
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_map_1450_);
lean_dec(v_o_1447_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1455_, 0, v_v_1449_);
lean_inc(v_k_1448_);
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1448_, v___x_1455_, v_map_1450_);
if (v_hasTrace_1451_ == 0)
{
lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1460_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1458_ = l_Lean_Name_isPrefixOf(v___x_1457_, v_k_1448_);
lean_dec(v_k_1448_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1460_ = v___x_1453_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1456_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*1, v___x_1458_);
return v___x_1460_;
}
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_k_1448_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1463_ = v___x_1453_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*1, v_hasTrace_1451_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_o_1466_, lean_object* v_k_1467_, lean_object* v_v_1468_){
_start:
{
uint8_t v_v_boxed_1469_; lean_object* v_res_1470_; 
v_v_boxed_1469_ = lean_unbox(v_v_1468_);
v_res_1470_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_o_1466_, v_k_1467_, v_v_boxed_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_opts_1471_, lean_object* v_opt_1472_, uint8_t v_val_1473_){
_start:
{
lean_object* v_name_1474_; lean_object* v___x_1475_; 
v_name_1474_ = lean_ctor_get(v_opt_1472_, 0);
lean_inc(v_name_1474_);
lean_dec_ref(v_opt_1472_);
v___x_1475_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_opts_1471_, v_name_1474_, v_val_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_opts_1476_, lean_object* v_opt_1477_, lean_object* v_val_1478_){
_start:
{
uint8_t v_val_boxed_1479_; lean_object* v_res_1480_; 
v_val_boxed_1479_ = lean_unbox(v_val_1478_);
v_res_1480_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_opts_1476_, v_opt_1477_, v_val_boxed_1479_);
return v_res_1480_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_declName_1490_, lean_object* v_declNameNonRec_1491_, lean_object* v___x_1492_, lean_object* v___f_1493_, lean_object* v_a_1494_, lean_object* v___x_1495_, lean_object* v_____r_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; uint8_t v___y_1511_; lean_object* v___y_1512_; uint8_t v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; uint8_t v___y_1570_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1598_; uint8_t v___y_1599_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1490_, v_declNameNonRec_1491_, v___x_1492_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___x_1706_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
lean_inc_ref(v___f_1493_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
v___x_1706_ = lean_apply_5(v___f_1493_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, lean_box(0));
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; uint8_t v___x_1708_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
if (v___x_1708_ == 0)
{
v___y_1669_ = v___y_1497_;
v___y_1670_ = v___y_1498_;
v___y_1671_ = v___y_1499_;
v___y_1672_ = v___y_1500_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
lean_inc(v_a_1667_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1667_);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
lean_inc(v___x_1495_);
v___x_1712_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1711_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_dec_ref_known(v___x_1712_, 1);
v___y_1669_ = v___y_1497_;
v___y_1670_ = v___y_1498_;
v___y_1671_ = v___y_1499_;
v___y_1672_ = v___y_1500_;
goto v___jp_1668_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_a_1667_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1667_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1721_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1706_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1706_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
v___jp_1668_:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1667_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
v___x_1675_ = lean_apply_5(v___f_1493_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, lean_box(0));
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; uint8_t v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
if (v___x_1677_ == 0)
{
v___y_1656_ = v_a_1674_;
v___y_1657_ = v___y_1669_;
v___y_1658_ = v___y_1670_;
v___y_1659_ = v___y_1671_;
v___y_1660_ = v___y_1672_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
lean_inc(v_a_1674_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_a_1674_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
lean_inc(v___x_1495_);
v___x_1681_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1680_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_dec_ref_known(v___x_1681_, 1);
v___y_1656_ = v_a_1674_;
v___y_1657_ = v___y_1669_;
v___y_1658_ = v___y_1670_;
v___y_1659_ = v___y_1671_;
v___y_1660_ = v___y_1672_;
goto v___jp_1655_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1674_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_a_1674_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1690_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1675_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1675_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1698_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1673_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1673_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1729_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1666_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1666_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
v___jp_1502_:
{
lean_object* v_fileName_1516_; lean_object* v_fileMap_1517_; lean_object* v_currRecDepth_1518_; lean_object* v_ref_1519_; lean_object* v_currNamespace_1520_; lean_object* v_openDecls_1521_; lean_object* v_initHeartbeats_1522_; lean_object* v_maxHeartbeats_1523_; lean_object* v_quotContext_1524_; lean_object* v_currMacroScope_1525_; lean_object* v_cancelTk_x3f_1526_; uint8_t v_suppressElabErrors_1527_; lean_object* v_inheritedTraceOptions_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_fileName_1516_ = lean_ctor_get(v___y_1514_, 0);
v_fileMap_1517_ = lean_ctor_get(v___y_1514_, 1);
v_currRecDepth_1518_ = lean_ctor_get(v___y_1514_, 3);
v_ref_1519_ = lean_ctor_get(v___y_1514_, 5);
v_currNamespace_1520_ = lean_ctor_get(v___y_1514_, 6);
v_openDecls_1521_ = lean_ctor_get(v___y_1514_, 7);
v_initHeartbeats_1522_ = lean_ctor_get(v___y_1514_, 8);
v_maxHeartbeats_1523_ = lean_ctor_get(v___y_1514_, 9);
v_quotContext_1524_ = lean_ctor_get(v___y_1514_, 10);
v_currMacroScope_1525_ = lean_ctor_get(v___y_1514_, 11);
v_cancelTk_x3f_1526_ = lean_ctor_get(v___y_1514_, 12);
v_suppressElabErrors_1527_ = lean_ctor_get_uint8(v___y_1514_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1528_ = lean_ctor_get(v___y_1514_, 13);
v___x_1529_ = l_Lean_maxRecDepth;
v___x_1530_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_1512_, v___x_1529_);
lean_inc_ref(v_inheritedTraceOptions_1528_);
lean_inc(v_cancelTk_x3f_1526_);
lean_inc(v_currMacroScope_1525_);
lean_inc(v_quotContext_1524_);
lean_inc(v_maxHeartbeats_1523_);
lean_inc(v_initHeartbeats_1522_);
lean_inc(v_openDecls_1521_);
lean_inc(v_currNamespace_1520_);
lean_inc(v_ref_1519_);
lean_inc(v_currRecDepth_1518_);
lean_inc_ref(v_fileMap_1517_);
lean_inc_ref(v_fileName_1516_);
v___x_1531_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1531_, 0, v_fileName_1516_);
lean_ctor_set(v___x_1531_, 1, v_fileMap_1517_);
lean_ctor_set(v___x_1531_, 2, v___y_1512_);
lean_ctor_set(v___x_1531_, 3, v_currRecDepth_1518_);
lean_ctor_set(v___x_1531_, 4, v___x_1530_);
lean_ctor_set(v___x_1531_, 5, v_ref_1519_);
lean_ctor_set(v___x_1531_, 6, v_currNamespace_1520_);
lean_ctor_set(v___x_1531_, 7, v_openDecls_1521_);
lean_ctor_set(v___x_1531_, 8, v_initHeartbeats_1522_);
lean_ctor_set(v___x_1531_, 9, v_maxHeartbeats_1523_);
lean_ctor_set(v___x_1531_, 10, v_quotContext_1524_);
lean_ctor_set(v___x_1531_, 11, v_currMacroScope_1525_);
lean_ctor_set(v___x_1531_, 12, v_cancelTk_x3f_1526_);
lean_ctor_set(v___x_1531_, 13, v_inheritedTraceOptions_1528_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*14, v___y_1511_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*14 + 1, v_suppressElabErrors_1527_);
v___x_1532_ = l_Lean_MVarId_refl(v___y_1505_, v___y_1513_, v___y_1506_, v___y_1508_, v___x_1531_, v___y_1515_);
lean_dec_ref_known(v___x_1531_, 14);
lean_dec_ref(v___y_1506_);
if (lean_obj_tag(v___x_1532_) == 0)
{
uint8_t v_hasTrace_1533_; 
lean_dec_ref_known(v___x_1532_, 1);
v_hasTrace_1533_ = lean_ctor_get_uint8(v___y_1510_, sizeof(void*)*1);
if (v_hasTrace_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec_ref(v___y_1510_);
lean_dec(v___x_1495_);
v___x_1534_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_1495_);
v___x_1536_ = l_Lean_Name_append(v___x_1535_, v___x_1495_);
v___x_1537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1509_, v___y_1510_, v___x_1536_);
lean_dec(v___x_1536_);
lean_dec_ref(v___y_1510_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec(v___x_1495_);
v___x_1538_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1540_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1539_, v___y_1503_, v___y_1508_, v___y_1507_, v___y_1504_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1540_, 1);
v___x_1541_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_a_1494_);
v_a_1542_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1540_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v___y_1510_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1550_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1532_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1532_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
v___jp_1558_:
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_bool_not(v___y_1570_);
if (v___x_1571_ == 0)
{
v___y_1503_ = v___y_1559_;
v___y_1504_ = v___y_1560_;
v___y_1505_ = v___y_1561_;
v___y_1506_ = v___y_1562_;
v___y_1507_ = v___y_1563_;
v___y_1508_ = v___y_1564_;
v___y_1509_ = v___y_1565_;
v___y_1510_ = v___y_1568_;
v___y_1511_ = v___y_1567_;
v___y_1512_ = v___y_1566_;
v___y_1513_ = v___y_1569_;
v___y_1514_ = v___y_1563_;
v___y_1515_ = v___y_1560_;
goto v___jp_1502_;
}
else
{
lean_object* v___x_1572_; lean_object* v_env_1573_; lean_object* v_nextMacroScope_1574_; lean_object* v_ngen_1575_; lean_object* v_auxDeclNGen_1576_; lean_object* v_traceState_1577_; lean_object* v_messages_1578_; lean_object* v_infoState_1579_; lean_object* v_snapshotTasks_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1590_; 
v___x_1572_ = lean_st_ref_take(v___y_1560_);
v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
v_nextMacroScope_1574_ = lean_ctor_get(v___x_1572_, 1);
v_ngen_1575_ = lean_ctor_get(v___x_1572_, 2);
v_auxDeclNGen_1576_ = lean_ctor_get(v___x_1572_, 3);
v_traceState_1577_ = lean_ctor_get(v___x_1572_, 4);
v_messages_1578_ = lean_ctor_get(v___x_1572_, 6);
v_infoState_1579_ = lean_ctor_get(v___x_1572_, 7);
v_snapshotTasks_1580_ = lean_ctor_get(v___x_1572_, 8);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1572_, 5);
lean_dec(v_unused_1591_);
v___x_1582_ = v___x_1572_;
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snapshotTasks_1580_);
lean_inc(v_infoState_1579_);
lean_inc(v_messages_1578_);
lean_inc(v_traceState_1577_);
lean_inc(v_auxDeclNGen_1576_);
lean_inc(v_ngen_1575_);
lean_inc(v_nextMacroScope_1574_);
lean_inc(v_env_1573_);
lean_dec(v___x_1572_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1584_ = l_Lean_Kernel_enableDiag(v_env_1573_, v___y_1567_);
v___x_1585_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 5, v___x_1585_);
lean_ctor_set(v___x_1582_, 0, v___x_1584_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_nextMacroScope_1574_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_ngen_1575_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_auxDeclNGen_1576_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_traceState_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 5, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1589_, 6, v_messages_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 7, v_infoState_1579_);
lean_ctor_set(v_reuseFailAlloc_1589_, 8, v_snapshotTasks_1580_);
v___x_1587_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_st_ref_set(v___y_1560_, v___x_1587_);
v___y_1503_ = v___y_1559_;
v___y_1504_ = v___y_1560_;
v___y_1505_ = v___y_1561_;
v___y_1506_ = v___y_1562_;
v___y_1507_ = v___y_1563_;
v___y_1508_ = v___y_1564_;
v___y_1509_ = v___y_1565_;
v___y_1510_ = v___y_1568_;
v___y_1511_ = v___y_1567_;
v___y_1512_ = v___y_1566_;
v___y_1513_ = v___y_1569_;
v___y_1514_ = v___y_1563_;
v___y_1515_ = v___y_1560_;
goto v___jp_1502_;
}
}
}
}
v___jp_1592_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v_foApprox_1602_; uint8_t v_ctxApprox_1603_; uint8_t v_quasiPatternApprox_1604_; uint8_t v_constApprox_1605_; uint8_t v_isDefEqStuckEx_1606_; uint8_t v_unificationHints_1607_; uint8_t v_proofIrrelevance_1608_; uint8_t v_assignSyntheticOpaque_1609_; uint8_t v_offsetCnstrs_1610_; uint8_t v_etaStruct_1611_; uint8_t v_univApprox_1612_; uint8_t v_iota_1613_; uint8_t v_beta_1614_; uint8_t v_proj_1615_; uint8_t v_zeta_1616_; uint8_t v_zetaDelta_1617_; uint8_t v_zetaUnused_1618_; uint8_t v_zetaHave_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1654_; 
v___x_1600_ = lean_st_ref_get(v___y_1594_);
v___x_1601_ = l_Lean_Meta_Context_config(v___y_1593_);
v_foApprox_1602_ = lean_ctor_get_uint8(v___x_1601_, 0);
v_ctxApprox_1603_ = lean_ctor_get_uint8(v___x_1601_, 1);
v_quasiPatternApprox_1604_ = lean_ctor_get_uint8(v___x_1601_, 2);
v_constApprox_1605_ = lean_ctor_get_uint8(v___x_1601_, 3);
v_isDefEqStuckEx_1606_ = lean_ctor_get_uint8(v___x_1601_, 4);
v_unificationHints_1607_ = lean_ctor_get_uint8(v___x_1601_, 5);
v_proofIrrelevance_1608_ = lean_ctor_get_uint8(v___x_1601_, 6);
v_assignSyntheticOpaque_1609_ = lean_ctor_get_uint8(v___x_1601_, 7);
v_offsetCnstrs_1610_ = lean_ctor_get_uint8(v___x_1601_, 8);
v_etaStruct_1611_ = lean_ctor_get_uint8(v___x_1601_, 10);
v_univApprox_1612_ = lean_ctor_get_uint8(v___x_1601_, 11);
v_iota_1613_ = lean_ctor_get_uint8(v___x_1601_, 12);
v_beta_1614_ = lean_ctor_get_uint8(v___x_1601_, 13);
v_proj_1615_ = lean_ctor_get_uint8(v___x_1601_, 14);
v_zeta_1616_ = lean_ctor_get_uint8(v___x_1601_, 15);
v_zetaDelta_1617_ = lean_ctor_get_uint8(v___x_1601_, 16);
v_zetaUnused_1618_ = lean_ctor_get_uint8(v___x_1601_, 17);
v_zetaHave_1619_ = lean_ctor_get_uint8(v___x_1601_, 18);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1621_ = v___x_1601_;
v_isShared_1622_ = v_isSharedCheck_1654_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1601_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1654_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
uint8_t v_trackZetaDelta_1623_; lean_object* v_zetaDeltaSet_1624_; lean_object* v_lctx_1625_; lean_object* v_localInstances_1626_; lean_object* v_defEqCtx_x3f_1627_; lean_object* v_synthPendingDepth_1628_; lean_object* v_canUnfold_x3f_1629_; uint8_t v_univApprox_1630_; uint8_t v_inTypeClassResolution_1631_; uint8_t v_cacheInferType_1632_; lean_object* v_options_1633_; lean_object* v_inheritedTraceOptions_1634_; lean_object* v_env_1635_; lean_object* v_config_1637_; 
v_trackZetaDelta_1623_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*7);
v_zetaDeltaSet_1624_ = lean_ctor_get(v___y_1593_, 1);
v_lctx_1625_ = lean_ctor_get(v___y_1593_, 2);
v_localInstances_1626_ = lean_ctor_get(v___y_1593_, 3);
v_defEqCtx_x3f_1627_ = lean_ctor_get(v___y_1593_, 4);
v_synthPendingDepth_1628_ = lean_ctor_get(v___y_1593_, 5);
v_canUnfold_x3f_1629_ = lean_ctor_get(v___y_1593_, 6);
v_univApprox_1630_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1631_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*7 + 2);
v_cacheInferType_1632_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*7 + 3);
v_options_1633_ = lean_ctor_get(v___y_1596_, 2);
v_inheritedTraceOptions_1634_ = lean_ctor_get(v___y_1596_, 13);
v_env_1635_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1635_);
lean_dec(v___x_1600_);
if (v_isShared_1622_ == 0)
{
v_config_1637_ = v___x_1621_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 0, v_foApprox_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 1, v_ctxApprox_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 2, v_quasiPatternApprox_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 3, v_constApprox_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 4, v_isDefEqStuckEx_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 5, v_unificationHints_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 6, v_proofIrrelevance_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 7, v_assignSyntheticOpaque_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 8, v_offsetCnstrs_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 10, v_etaStruct_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 11, v_univApprox_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 12, v_iota_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 13, v_beta_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 14, v_proj_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 15, v_zeta_1616_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 16, v_zetaDelta_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 17, v_zetaUnused_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1653_, 18, v_zetaHave_1619_);
v_config_1637_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
uint64_t v___x_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v___x_1642_; uint64_t v_key_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; 
lean_ctor_set_uint8(v_config_1637_, 9, v___y_1599_);
v___x_1638_ = l_Lean_Meta_Context_configKey(v___y_1593_);
v___x_1639_ = 3ULL;
v___x_1640_ = lean_uint64_shift_right(v___x_1638_, v___x_1639_);
v___x_1641_ = lean_uint64_shift_left(v___x_1640_, v___x_1639_);
v___x_1642_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1599_);
v_key_1643_ = lean_uint64_lor(v___x_1641_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1644_, 0, v_config_1637_);
lean_ctor_set_uint64(v___x_1644_, sizeof(void*)*1, v_key_1643_);
lean_inc(v_canUnfold_x3f_1629_);
lean_inc(v_synthPendingDepth_1628_);
lean_inc(v_defEqCtx_x3f_1627_);
lean_inc_ref(v_localInstances_1626_);
lean_inc_ref(v_lctx_1625_);
lean_inc(v_zetaDeltaSet_1624_);
v___x_1645_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_zetaDeltaSet_1624_);
lean_ctor_set(v___x_1645_, 2, v_lctx_1625_);
lean_ctor_set(v___x_1645_, 3, v_localInstances_1626_);
lean_ctor_set(v___x_1645_, 4, v_defEqCtx_x3f_1627_);
lean_ctor_set(v___x_1645_, 5, v_synthPendingDepth_1628_);
lean_ctor_set(v___x_1645_, 6, v_canUnfold_x3f_1629_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*7, v_trackZetaDelta_1623_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*7 + 1, v_univApprox_1630_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1631_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*7 + 3, v_cacheInferType_1632_);
v___x_1646_ = l_Lean_Meta_smartUnfolding;
v___x_1647_ = 0;
lean_inc_ref(v_options_1633_);
v___x_1648_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1633_, v___x_1646_, v___x_1647_);
v___x_1649_ = l_Lean_diagnostics;
v___x_1650_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1648_, v___x_1649_);
v___x_1651_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1635_);
lean_dec_ref(v_env_1635_);
if (v___x_1651_ == 0)
{
if (v___x_1650_ == 0)
{
uint8_t v___x_1652_; 
v___x_1652_ = 1;
lean_inc_ref(v_options_1633_);
v___y_1559_ = v___y_1593_;
v___y_1560_ = v___y_1594_;
v___y_1561_ = v___y_1595_;
v___y_1562_ = v___x_1645_;
v___y_1563_ = v___y_1596_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v_inheritedTraceOptions_1634_;
v___y_1566_ = v___x_1648_;
v___y_1567_ = v___x_1650_;
v___y_1568_ = v_options_1633_;
v___y_1569_ = v___y_1598_;
v___y_1570_ = v___x_1652_;
goto v___jp_1558_;
}
else
{
lean_inc_ref(v_options_1633_);
v___y_1559_ = v___y_1593_;
v___y_1560_ = v___y_1594_;
v___y_1561_ = v___y_1595_;
v___y_1562_ = v___x_1645_;
v___y_1563_ = v___y_1596_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v_inheritedTraceOptions_1634_;
v___y_1566_ = v___x_1648_;
v___y_1567_ = v___x_1650_;
v___y_1568_ = v_options_1633_;
v___y_1569_ = v___y_1598_;
v___y_1570_ = v___x_1651_;
goto v___jp_1558_;
}
}
else
{
lean_inc_ref(v_options_1633_);
v___y_1559_ = v___y_1593_;
v___y_1560_ = v___y_1594_;
v___y_1561_ = v___y_1595_;
v___y_1562_ = v___x_1645_;
v___y_1563_ = v___y_1596_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v_inheritedTraceOptions_1634_;
v___y_1566_ = v___x_1648_;
v___y_1567_ = v___x_1650_;
v___y_1568_ = v_options_1633_;
v___y_1569_ = v___y_1598_;
v___y_1570_ = v___x_1650_;
goto v___jp_1558_;
}
}
}
}
v___jp_1655_:
{
lean_object* v___x_1661_; uint8_t v_transparency_1662_; uint8_t v___x_1663_; uint8_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1661_ = l_Lean_Meta_Context_config(v___y_1657_);
v_transparency_1662_ = lean_ctor_get_uint8(v___x_1661_, 9);
lean_dec_ref(v___x_1661_);
v___x_1663_ = 0;
v___x_1664_ = 1;
v___x_1665_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1662_, v___x_1663_);
if (v___x_1665_ == 0)
{
v___y_1593_ = v___y_1657_;
v___y_1594_ = v___y_1660_;
v___y_1595_ = v___y_1656_;
v___y_1596_ = v___y_1659_;
v___y_1597_ = v___y_1658_;
v___y_1598_ = v___x_1664_;
v___y_1599_ = v_transparency_1662_;
goto v___jp_1592_;
}
else
{
v___y_1593_ = v___y_1657_;
v___y_1594_ = v___y_1660_;
v___y_1595_ = v___y_1656_;
v___y_1596_ = v___y_1659_;
v___y_1597_ = v___y_1658_;
v___y_1598_ = v___x_1664_;
v___y_1599_ = v___x_1663_;
goto v___jp_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1737_, lean_object* v_declNameNonRec_1738_, lean_object* v___x_1739_, lean_object* v___f_1740_, lean_object* v_a_1741_, lean_object* v___x_1742_, lean_object* v_____r_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1737_, v_declNameNonRec_1738_, v___x_1739_, v___f_1740_, v_a_1741_, v___x_1742_, v_____r_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8));
v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_declName_1767_, lean_object* v_a_1768_, lean_object* v___x_1769_, lean_object* v_declNameNonRec_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___y_1777_; lean_object* v___y_1778_; uint8_t v___y_1779_; lean_object* v___y_1789_; lean_object* v_a_1790_; lean_object* v___y_1794_; lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1768_, v___x_1769_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1825_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6));
v___f_1799_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7));
v___x_1800_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1798_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1825_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1825_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = l_Lean_Expr_mvarId_x21(v_a_1797_);
v___x_1806_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_del_object(v___x_1803_);
v___x_1807_ = lean_box(0);
lean_inc(v_declName_1767_);
v___x_1808_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1767_, v_declNameNonRec_1770_, v___x_1805_, v___f_1799_, v_a_1797_, v___x_1798_, v___x_1807_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
v___y_1794_ = v___x_1808_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
lean_inc(v___x_1805_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1805_);
v___x_1811_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1809_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1798_, v___x_1812_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
lean_inc(v_declName_1767_);
v___x_1815_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1767_, v_declNameNonRec_1770_, v___x_1805_, v___f_1799_, v_a_1797_, v___x_1798_, v_a_1814_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
v___y_1794_ = v___x_1815_;
goto v___jp_1793_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v___x_1805_);
lean_dec(v_a_1797_);
lean_dec(v_declNameNonRec_1770_);
v_a_1816_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1813_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1813_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
lean_inc(v_a_1816_);
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v___y_1789_ = v___x_1821_;
v_a_1790_ = v_a_1816_;
goto v___jp_1788_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1770_);
v___y_1794_ = v___x_1796_;
goto v___jp_1793_;
}
v___jp_1776_:
{
if (v___y_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec_ref(v___y_1778_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_1781_ = l_Lean_MessageData_ofConstName(v_declName_1767_, v___y_1779_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_Exception_toMessageData(v___y_1777_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1786_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1787_;
}
else
{
lean_dec_ref(v___y_1777_);
lean_dec(v_declName_1767_);
return v___y_1778_;
}
}
v___jp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_Exception_isInterrupt(v_a_1790_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
lean_inc_ref(v_a_1790_);
v___x_1792_ = l_Lean_Exception_isRuntime(v_a_1790_);
v___y_1777_ = v_a_1790_;
v___y_1778_ = v___y_1789_;
v___y_1779_ = v___x_1792_;
goto v___jp_1776_;
}
else
{
v___y_1777_ = v_a_1790_;
v___y_1778_ = v___y_1789_;
v___y_1779_ = v___x_1791_;
goto v___jp_1776_;
}
}
v___jp_1793_:
{
if (lean_obj_tag(v___y_1794_) == 0)
{
lean_dec(v_declName_1767_);
return v___y_1794_;
}
else
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___y_1794_, 0);
lean_inc(v_a_1795_);
v___y_1789_ = v___y_1794_;
v_a_1790_ = v_a_1795_;
goto v___jp_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_declName_1826_, lean_object* v_a_1827_, lean_object* v___x_1828_, lean_object* v_declNameNonRec_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_1826_, v_a_1827_, v___x_1828_, v_declNameNonRec_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = l_List_reverse___redArg(v_a_1837_);
return v___x_1838_;
}
else
{
lean_object* v_head_1839_; lean_object* v_tail_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1849_; 
v_head_1839_ = lean_ctor_get(v_a_1836_, 0);
v_tail_1840_ = lean_ctor_get(v_a_1836_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1842_ = v_a_1836_;
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_tail_1840_);
lean_inc(v_head_1839_);
lean_dec(v_a_1836_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = l_Lean_mkLevelParam(v_head_1839_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v_a_1837_);
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_a_1837_);
v___x_1846_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
v_a_1836_ = v_tail_1840_;
v_a_1837_ = v___x_1846_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_levelParams_1850_, lean_object* v_declName_1851_, lean_object* v_declNameNonRec_1852_, lean_object* v_name_1853_, lean_object* v_xs_1854_, lean_object* v_body_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; lean_object* v_us_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = lean_box(0);
lean_inc(v_levelParams_1850_);
v_us_1862_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1850_, v___x_1861_);
lean_inc(v_declName_1851_);
v___x_1863_ = l_Lean_mkConst(v_declName_1851_, v_us_1862_);
v___x_1864_ = l_Lean_mkAppN(v___x_1863_, v_xs_1854_);
v___x_1865_ = l_Lean_Meta_mkEq(v___x_1864_, v_body_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___f_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_n(v_a_1866_, 2);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = lean_box(0);
v___f_1868_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1868_, 0, v_declName_1851_);
lean_closure_set(v___f_1868_, 1, v_a_1866_);
lean_closure_set(v___f_1868_, 2, v___x_1867_);
lean_closure_set(v___f_1868_, 3, v_declNameNonRec_1852_);
v___x_1869_ = 0;
v___x_1870_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_1868_, v___x_1869_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = 1;
v___x_1873_ = 1;
v___x_1874_ = l_Lean_Meta_mkForallFVars(v_xs_1854_, v_a_1866_, v___x_1869_, v___x_1872_, v___x_1872_, v___x_1873_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_Lean_Meta_letToHave(v_a_1875_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l_Lean_Meta_mkLambdaFVars(v_xs_1854_, v_a_1871_, v___x_1869_, v___x_1872_, v___x_1869_, v___x_1872_, v___x_1873_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
lean_inc(v_name_1853_);
v___x_1880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1880_, 0, v_name_1853_);
lean_ctor_set(v___x_1880_, 1, v_levelParams_1850_);
lean_ctor_set(v___x_1880_, 2, v_a_1877_);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_name_1853_);
lean_ctor_set(v___x_1881_, 1, v___x_1861_);
v___x_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v_a_1879_);
lean_ctor_set(v___x_1882_, 2, v___x_1881_);
v___x_1883_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_1882_, v___y_1859_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_addDecl(v_a_1884_, v___x_1869_, v___y_1858_, v___y_1859_);
return v___x_1885_;
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1877_);
lean_dec(v_name_1853_);
lean_dec(v_levelParams_1850_);
v_a_1886_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1878_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1878_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1871_);
lean_dec(v_name_1853_);
lean_dec(v_levelParams_1850_);
v_a_1894_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1876_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1876_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1871_);
lean_dec(v_name_1853_);
lean_dec(v_levelParams_1850_);
v_a_1902_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1874_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1874_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_a_1866_);
lean_dec(v_name_1853_);
lean_dec(v_levelParams_1850_);
v_a_1910_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1870_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1870_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_name_1853_);
lean_dec(v_declNameNonRec_1852_);
lean_dec(v_declName_1851_);
lean_dec(v_levelParams_1850_);
v_a_1918_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1865_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1865_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_levelParams_1926_, lean_object* v_declName_1927_, lean_object* v_declNameNonRec_1928_, lean_object* v_name_1929_, lean_object* v_xs_1930_, lean_object* v_body_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_1926_, v_declName_1927_, v_declNameNonRec_1928_, v_name_1929_, v_xs_1930_, v_body_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec_ref(v_xs_1930_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1938_, lean_object* v_info_1939_, lean_object* v_name_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v_levelParams_1947_; lean_object* v_value_1948_; lean_object* v_declNameNonRec_1949_; lean_object* v_fileName_1950_; lean_object* v_fileMap_1951_; lean_object* v_options_1952_; lean_object* v_currRecDepth_1953_; lean_object* v_ref_1954_; lean_object* v_currNamespace_1955_; lean_object* v_openDecls_1956_; lean_object* v_initHeartbeats_1957_; lean_object* v_maxHeartbeats_1958_; lean_object* v_quotContext_1959_; lean_object* v_currMacroScope_1960_; lean_object* v_cancelTk_x3f_1961_; uint8_t v_suppressElabErrors_1962_; lean_object* v_inheritedTraceOptions_1963_; lean_object* v_env_1964_; lean_object* v___f_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v_fileName_1972_; lean_object* v_fileMap_1973_; lean_object* v_currRecDepth_1974_; lean_object* v_ref_1975_; lean_object* v_currNamespace_1976_; lean_object* v_openDecls_1977_; lean_object* v_initHeartbeats_1978_; lean_object* v_maxHeartbeats_1979_; lean_object* v_quotContext_1980_; lean_object* v_currMacroScope_1981_; lean_object* v_cancelTk_x3f_1982_; uint8_t v_suppressElabErrors_1983_; lean_object* v_inheritedTraceOptions_1984_; lean_object* v___y_1985_; uint8_t v___y_1991_; uint8_t v___x_2013_; 
v___x_1946_ = lean_st_ref_get(v_a_1944_);
v_levelParams_1947_ = lean_ctor_get(v_info_1939_, 1);
lean_inc(v_levelParams_1947_);
v_value_1948_ = lean_ctor_get(v_info_1939_, 3);
lean_inc_ref(v_value_1948_);
v_declNameNonRec_1949_ = lean_ctor_get(v_info_1939_, 5);
lean_inc(v_declNameNonRec_1949_);
lean_dec_ref(v_info_1939_);
v_fileName_1950_ = lean_ctor_get(v_a_1943_, 0);
v_fileMap_1951_ = lean_ctor_get(v_a_1943_, 1);
v_options_1952_ = lean_ctor_get(v_a_1943_, 2);
v_currRecDepth_1953_ = lean_ctor_get(v_a_1943_, 3);
v_ref_1954_ = lean_ctor_get(v_a_1943_, 5);
v_currNamespace_1955_ = lean_ctor_get(v_a_1943_, 6);
v_openDecls_1956_ = lean_ctor_get(v_a_1943_, 7);
v_initHeartbeats_1957_ = lean_ctor_get(v_a_1943_, 8);
v_maxHeartbeats_1958_ = lean_ctor_get(v_a_1943_, 9);
v_quotContext_1959_ = lean_ctor_get(v_a_1943_, 10);
v_currMacroScope_1960_ = lean_ctor_get(v_a_1943_, 11);
v_cancelTk_x3f_1961_ = lean_ctor_get(v_a_1943_, 12);
v_suppressElabErrors_1962_ = lean_ctor_get_uint8(v_a_1943_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1963_ = lean_ctor_get(v_a_1943_, 13);
v_env_1964_ = lean_ctor_get(v___x_1946_, 0);
lean_inc_ref(v_env_1964_);
lean_dec(v___x_1946_);
v___f_1965_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 4);
lean_closure_set(v___f_1965_, 0, v_levelParams_1947_);
lean_closure_set(v___f_1965_, 1, v_declName_1938_);
lean_closure_set(v___f_1965_, 2, v_declNameNonRec_1949_);
lean_closure_set(v___f_1965_, 3, v_name_1940_);
v___x_1966_ = 0;
v___x_1967_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_1952_);
v___x_1968_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1952_, v___x_1967_, v___x_1966_);
v___x_1969_ = l_Lean_diagnostics;
v___x_1970_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1968_, v___x_1969_);
v___x_2013_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1964_);
lean_dec_ref(v_env_1964_);
if (v___x_2013_ == 0)
{
if (v___x_1970_ == 0)
{
uint8_t v___x_2014_; 
v___x_2014_ = 1;
v___y_1991_ = v___x_2014_;
goto v___jp_1990_;
}
else
{
v___y_1991_ = v___x_2013_;
goto v___jp_1990_;
}
}
else
{
v___y_1991_ = v___x_1970_;
goto v___jp_1990_;
}
v___jp_1971_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1986_ = l_Lean_maxRecDepth;
v___x_1987_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_1968_, v___x_1986_);
lean_inc_ref(v_inheritedTraceOptions_1984_);
lean_inc(v_cancelTk_x3f_1982_);
lean_inc(v_currMacroScope_1981_);
lean_inc(v_quotContext_1980_);
lean_inc(v_maxHeartbeats_1979_);
lean_inc(v_initHeartbeats_1978_);
lean_inc(v_openDecls_1977_);
lean_inc(v_currNamespace_1976_);
lean_inc(v_ref_1975_);
lean_inc(v_currRecDepth_1974_);
lean_inc_ref(v_fileMap_1973_);
lean_inc_ref(v_fileName_1972_);
v___x_1988_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1988_, 0, v_fileName_1972_);
lean_ctor_set(v___x_1988_, 1, v_fileMap_1973_);
lean_ctor_set(v___x_1988_, 2, v___x_1968_);
lean_ctor_set(v___x_1988_, 3, v_currRecDepth_1974_);
lean_ctor_set(v___x_1988_, 4, v___x_1987_);
lean_ctor_set(v___x_1988_, 5, v_ref_1975_);
lean_ctor_set(v___x_1988_, 6, v_currNamespace_1976_);
lean_ctor_set(v___x_1988_, 7, v_openDecls_1977_);
lean_ctor_set(v___x_1988_, 8, v_initHeartbeats_1978_);
lean_ctor_set(v___x_1988_, 9, v_maxHeartbeats_1979_);
lean_ctor_set(v___x_1988_, 10, v_quotContext_1980_);
lean_ctor_set(v___x_1988_, 11, v_currMacroScope_1981_);
lean_ctor_set(v___x_1988_, 12, v_cancelTk_x3f_1982_);
lean_ctor_set(v___x_1988_, 13, v_inheritedTraceOptions_1984_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*14, v___x_1970_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*14 + 1, v_suppressElabErrors_1983_);
v___x_1989_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_1948_, v___f_1965_, v___x_1966_, v_a_1941_, v_a_1942_, v___x_1988_, v___y_1985_);
lean_dec_ref_known(v___x_1988_, 14);
return v___x_1989_;
}
v___jp_1990_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_bool_not(v___y_1991_);
if (v___x_1992_ == 0)
{
v_fileName_1972_ = v_fileName_1950_;
v_fileMap_1973_ = v_fileMap_1951_;
v_currRecDepth_1974_ = v_currRecDepth_1953_;
v_ref_1975_ = v_ref_1954_;
v_currNamespace_1976_ = v_currNamespace_1955_;
v_openDecls_1977_ = v_openDecls_1956_;
v_initHeartbeats_1978_ = v_initHeartbeats_1957_;
v_maxHeartbeats_1979_ = v_maxHeartbeats_1958_;
v_quotContext_1980_ = v_quotContext_1959_;
v_currMacroScope_1981_ = v_currMacroScope_1960_;
v_cancelTk_x3f_1982_ = v_cancelTk_x3f_1961_;
v_suppressElabErrors_1983_ = v_suppressElabErrors_1962_;
v_inheritedTraceOptions_1984_ = v_inheritedTraceOptions_1963_;
v___y_1985_ = v_a_1944_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_traceState_1998_; lean_object* v_messages_1999_; lean_object* v_infoState_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
v___x_1993_ = lean_st_ref_take(v_a_1944_);
v_env_1994_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1993_, 3);
v_traceState_1998_ = lean_ctor_get(v___x_1993_, 4);
v_messages_1999_ = lean_ctor_get(v___x_1993_, 6);
v_infoState_2000_ = lean_ctor_get(v___x_1993_, 7);
v_snapshotTasks_2001_ = lean_ctor_get(v___x_1993_, 8);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v___x_1993_, 5);
lean_dec(v_unused_2012_);
v___x_2003_ = v___x_1993_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snapshotTasks_2001_);
lean_inc(v_infoState_2000_);
lean_inc(v_messages_1999_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1993_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = l_Lean_Kernel_enableDiag(v_env_1994_, v___x_1970_);
v___x_2006_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 5, v___x_2006_);
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_traceState_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2010_, 6, v_messages_1999_);
lean_ctor_set(v_reuseFailAlloc_2010_, 7, v_infoState_2000_);
lean_ctor_set(v_reuseFailAlloc_2010_, 8, v_snapshotTasks_2001_);
v___x_2008_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_st_ref_set(v_a_1944_, v___x_2008_);
v_fileName_1972_ = v_fileName_1950_;
v_fileMap_1973_ = v_fileMap_1951_;
v_currRecDepth_1974_ = v_currRecDepth_1953_;
v_ref_1975_ = v_ref_1954_;
v_currNamespace_1976_ = v_currNamespace_1955_;
v_openDecls_1977_ = v_openDecls_1956_;
v_initHeartbeats_1978_ = v_initHeartbeats_1957_;
v_maxHeartbeats_1979_ = v_maxHeartbeats_1958_;
v_quotContext_1980_ = v_quotContext_1959_;
v_currMacroScope_1981_ = v_currMacroScope_1960_;
v_cancelTk_x3f_1982_ = v_cancelTk_x3f_1961_;
v_suppressElabErrors_1983_ = v_suppressElabErrors_1962_;
v_inheritedTraceOptions_1984_ = v_inheritedTraceOptions_1963_;
v___y_1985_ = v_a_1944_;
goto v___jp_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2015_, lean_object* v_info_2016_, lean_object* v_name_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2015_, v_info_2016_, v_name_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2024_, lean_object* v_info_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v_env_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = lean_st_ref_get(v_a_2029_);
v_env_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2032_);
lean_dec(v___x_2031_);
v___x_2033_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_2024_, 2);
v___x_2034_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2032_, v_declName_2024_, v___x_2033_);
lean_inc_n(v___x_2034_, 2);
v___x_2035_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2035_, 0, v_declName_2024_);
lean_closure_set(v___x_2035_, 1, v_info_2025_);
lean_closure_set(v___x_2035_, 2, v___x_2034_);
v___x_2036_ = l_Lean_Meta_realizeConst(v_declName_2024_, v___x_2034_, v___x_2035_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2044_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2034_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2034_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v___x_2034_);
v_a_2045_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2036_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2036_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2053_, lean_object* v_info_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2053_, v_info_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_env_2069_; lean_object* v_env_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2067_ = lean_st_ref_get(v_a_2065_);
v___x_2068_ = lean_st_ref_get(v_a_2065_);
v_env_2069_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_env_2069_);
lean_dec(v___x_2067_);
v_env_2070_ = lean_ctor_get(v___x_2068_, 0);
lean_inc_ref_n(v_env_2070_, 2);
lean_dec(v___x_2068_);
v___x_2071_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2061_);
v___x_2072_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2069_, v_declName_2061_, v___x_2071_);
v___x_2073_ = 1;
lean_inc(v___x_2072_);
v___x_2074_ = l_Lean_Environment_contains(v_env_2070_, v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v_toEnvExtension_2076_; lean_object* v_asyncMode_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v___x_2072_);
v___x_2075_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2076_ = lean_ctor_get(v___x_2075_, 0);
v_asyncMode_2077_ = lean_ctor_get(v_toEnvExtension_2076_, 2);
v___x_2078_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2079_ = 0;
lean_inc(v_declName_2061_);
v___x_2080_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2078_, v___x_2075_, v_env_2070_, v_declName_2061_, v_asyncMode_2077_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 1)
{
lean_object* v_val_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2105_; 
v_val_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_val_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2061_, v_val_2081_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2096_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v_a_2086_);
v___x_2091_ = v___x_2083_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2091_);
v___x_2093_ = v___x_2088_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_2083_);
v_a_2097_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2085_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2085_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v___x_2080_);
lean_dec(v_declName_2061_);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec_ref(v_env_2070_);
lean_dec(v_declName_2061_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2072_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2120_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2122_;
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
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_3225328890____hygCtx___hyg_2_();
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
