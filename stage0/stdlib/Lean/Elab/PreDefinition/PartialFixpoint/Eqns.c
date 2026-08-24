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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_74_, uint8_t v___x_75_, uint8_t v_____do__lift_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
if (v_____do__lift_76_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_box(v___x_74_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_box(v___x_75_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_86_, lean_object* v___x_87_, lean_object* v_____do__lift_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_3405__boxed_94_; uint8_t v___x_3406__boxed_95_; uint8_t v_____do__lift_3407__boxed_96_; lean_object* v_res_97_; 
v___x_3405__boxed_94_ = lean_unbox(v___x_86_);
v___x_3406__boxed_95_ = lean_unbox(v___x_87_);
v_____do__lift_3407__boxed_96_ = lean_unbox(v_____do__lift_88_);
v_res_97_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_3405__boxed_94_, v___x_3406__boxed_95_, v_____do__lift_3407__boxed_96_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_eq(v_i_99_, v_stop_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v_kind_103_; uint8_t v___x_104_; 
v___x_102_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
v_kind_103_ = lean_ctor_get_uint8(v___x_102_, sizeof(void*)*9);
v___x_104_ = l_Lean_Elab_DefKind_isTheorem(v_kind_103_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_99_, v___x_106_);
v_i_99_ = v___x_107_;
goto _start;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_stop_112_){
_start:
{
size_t v_i_boxed_113_; size_t v_stop_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_i_boxed_113_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_stop_boxed_114_ = lean_unbox_usize(v_stop_112_);
lean_dec(v_stop_112_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_110_, v_i_boxed_113_, v_stop_boxed_114_);
lean_dec_ref(v_as_110_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_117_, lean_object* v_declNameNonRec_118_, lean_object* v_fixedParamPerms_119_, lean_object* v_fixpointType_120_, lean_object* v_as_121_, size_t v_i_122_, size_t v_stop_123_, lean_object* v_b_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_eq(v_i_122_, v_stop_123_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v_levelParams_127_; lean_object* v_declName_128_; lean_object* v_type_129_; lean_object* v_value_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; 
v___x_126_ = lean_array_uget_borrowed(v_as_121_, v_i_122_);
v_levelParams_127_ = lean_ctor_get(v___x_126_, 1);
v_declName_128_ = lean_ctor_get(v___x_126_, 3);
v_type_129_ = lean_ctor_get(v___x_126_, 6);
v_value_130_ = lean_ctor_get(v___x_126_, 7);
v___x_131_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc_ref(v_fixpointType_120_);
lean_inc_ref(v_fixedParamPerms_119_);
lean_inc(v_declNameNonRec_118_);
lean_inc_ref(v___x_117_);
lean_inc_ref(v_value_130_);
lean_inc_ref(v_type_129_);
lean_inc(v_levelParams_127_);
lean_inc_n(v_declName_128_, 2);
v___x_132_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_132_, 0, v_declName_128_);
lean_ctor_set(v___x_132_, 1, v_levelParams_127_);
lean_ctor_set(v___x_132_, 2, v_type_129_);
lean_ctor_set(v___x_132_, 3, v_value_130_);
lean_ctor_set(v___x_132_, 4, v___x_117_);
lean_ctor_set(v___x_132_, 5, v_declNameNonRec_118_);
lean_ctor_set(v___x_132_, 6, v_fixedParamPerms_119_);
lean_ctor_set(v___x_132_, 7, v_fixpointType_120_);
v___x_133_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_131_, v_b_124_, v_declName_128_, v___x_132_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_i_122_, v___x_134_);
v_i_122_ = v___x_135_;
v_b_124_ = v___x_133_;
goto _start;
}
else
{
lean_dec_ref(v_fixpointType_120_);
lean_dec_ref(v_fixedParamPerms_119_);
lean_dec(v_declNameNonRec_118_);
lean_dec_ref(v___x_117_);
return v_b_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_137_, lean_object* v_declNameNonRec_138_, lean_object* v_fixedParamPerms_139_, lean_object* v_fixpointType_140_, lean_object* v_as_141_, lean_object* v_i_142_, lean_object* v_stop_143_, lean_object* v_b_144_){
_start:
{
size_t v_i_boxed_145_; size_t v_stop_boxed_146_; lean_object* v_res_147_; 
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_143_);
lean_dec(v_stop_143_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_137_, v_declNameNonRec_138_, v_fixedParamPerms_139_, v_fixpointType_140_, v_as_141_, v_i_boxed_145_, v_stop_boxed_146_, v_b_144_);
lean_dec_ref(v_as_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_148_, size_t v_i_149_, lean_object* v_bs_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_lt(v_i_149_, v_sz_148_);
if (v___x_151_ == 0)
{
return v_bs_150_;
}
else
{
lean_object* v_v_152_; lean_object* v_declName_153_; lean_object* v___x_154_; lean_object* v_bs_x27_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; 
v_v_152_ = lean_array_uget_borrowed(v_bs_150_, v_i_149_);
v_declName_153_ = lean_ctor_get(v_v_152_, 3);
lean_inc(v_declName_153_);
v___x_154_ = lean_unsigned_to_nat(0u);
v_bs_x27_155_ = lean_array_uset(v_bs_150_, v_i_149_, v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_149_, v___x_156_);
v___x_158_ = lean_array_uset(v_bs_x27_155_, v_i_149_, v_declName_153_);
v_i_149_ = v___x_157_;
v_bs_150_ = v___x_158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_160_, lean_object* v_i_161_, lean_object* v_bs_162_){
_start:
{
size_t v_sz_boxed_163_; size_t v_i_boxed_164_; lean_object* v_res_165_; 
v_sz_boxed_163_ = lean_unbox_usize(v_sz_160_);
lean_dec(v_sz_160_);
v_i_boxed_164_ = lean_unbox_usize(v_i_161_);
lean_dec(v_i_161_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_163_, v_i_boxed_164_, v_bs_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_166_, size_t v_i_167_, size_t v_stop_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_eq(v_i_167_, v_stop_168_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v_declName_175_; lean_object* v___x_176_; 
v___x_174_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
v_declName_175_ = lean_ctor_get(v___x_174_, 3);
lean_inc(v_declName_175_);
v___x_176_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_175_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; size_t v___x_178_; size_t v___x_179_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_167_, v___x_178_);
v_i_167_ = v___x_179_;
v_b_169_ = v_a_177_;
goto _start;
}
else
{
return v___x_176_;
}
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v_b_169_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_182_, lean_object* v_i_183_, lean_object* v_stop_184_, lean_object* v_b_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
size_t v_i_boxed_189_; size_t v_stop_boxed_190_; lean_object* v_res_191_; 
v_i_boxed_189_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_stop_boxed_190_ = lean_unbox_usize(v_stop_184_);
lean_dec(v_stop_184_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_182_, v_i_boxed_189_, v_stop_boxed_190_, v_b_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec_ref(v_as_182_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_192_, lean_object* v_as_193_, size_t v_i_194_, size_t v_stop_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_usize_dec_eq(v_i_194_, v_stop_195_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v_type_207_; uint8_t v___x_208_; uint8_t v_a_210_; lean_object* v___x_213_; 
v___x_206_ = lean_array_uget_borrowed(v_as_193_, v_i_194_);
v_type_207_ = lean_ctor_get(v___x_206_, 6);
v___x_208_ = 1;
lean_inc_ref(v_type_207_);
v___x_213_ = l_Lean_Meta_isProp(v_type_207_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = lean_unbox(v_a_214_);
lean_dec(v_a_214_);
if (v___x_215_ == 0)
{
v_a_210_ = v___x_192_;
goto v___jp_209_;
}
else
{
goto v___jp_201_;
}
}
else
{
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_216_; uint8_t v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_213_, 1);
v___x_217_ = lean_unbox(v_a_216_);
lean_dec(v_a_216_);
v_a_210_ = v___x_217_;
goto v___jp_209_;
}
else
{
return v___x_213_;
}
}
v___jp_209_:
{
if (v_a_210_ == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_box(v___x_208_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
else
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = 0;
v___x_219_ = lean_box(v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
v___jp_201_:
{
size_t v___x_202_; size_t v___x_203_; 
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_add(v_i_194_, v___x_202_);
v_i_194_ = v___x_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_221_, lean_object* v_as_222_, lean_object* v_i_223_, lean_object* v_stop_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
uint8_t v___x_3510__boxed_230_; size_t v_i_boxed_231_; size_t v_stop_boxed_232_; lean_object* v_res_233_; 
v___x_3510__boxed_230_ = lean_unbox(v___x_221_);
v_i_boxed_231_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_stop_boxed_232_ = lean_unbox_usize(v_stop_224_);
lean_dec(v_stop_224_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_3510__boxed_230_, v_as_222_, v_i_boxed_231_, v_stop_boxed_232_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec_ref(v_as_222_);
return v_res_233_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
v___x_240_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_ctor_set(v___x_240_, 3, v___x_239_);
lean_ctor_set(v___x_240_, 4, v___x_239_);
lean_ctor_set(v___x_240_, 5, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_241_, lean_object* v_declNameNonRec_242_, lean_object* v_fixedParamPerms_243_, lean_object* v_fixpointType_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_nextMacroScope_254_; lean_object* v_ngen_255_; lean_object* v_auxDeclNGen_256_; lean_object* v_traceState_257_; lean_object* v_messages_258_; lean_object* v_infoState_259_; lean_object* v_snapshotTasks_260_; lean_object* v___y_261_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___y_288_; lean_object* v___y_329_; uint8_t v___x_330_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_get_size(v_preDefs_241_);
v___x_330_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_330_ == 0)
{
goto v___jp_317_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_box(0);
v___x_332_ = lean_nat_dec_le(v___x_286_, v___x_286_);
if (v___x_332_ == 0)
{
if (v___x_330_ == 0)
{
goto v___jp_317_;
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_286_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_241_, v___x_333_, v___x_334_, v___x_331_, v_a_247_, v_a_248_);
v___y_329_ = v___x_335_;
goto v___jp_328_;
}
}
else
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_286_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_241_, v___x_336_, v___x_337_, v___x_331_, v_a_247_, v_a_248_);
v___y_329_ = v___x_338_;
goto v___jp_328_;
}
}
v___jp_250_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v_zetaDeltaFVarIds_267_; lean_object* v_postponed_268_; lean_object* v_diag_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
v___x_262_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
v___x_263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v_nextMacroScope_254_);
lean_ctor_set(v___x_263_, 2, v_ngen_255_);
lean_ctor_set(v___x_263_, 3, v_auxDeclNGen_256_);
lean_ctor_set(v___x_263_, 4, v_traceState_257_);
lean_ctor_set(v___x_263_, 5, v___x_262_);
lean_ctor_set(v___x_263_, 6, v_messages_258_);
lean_ctor_set(v___x_263_, 7, v_infoState_259_);
lean_ctor_set(v___x_263_, 8, v_snapshotTasks_260_);
v___x_264_ = lean_st_ref_put(v_a_248_, v___x_263_);
v___x_265_ = lean_st_ref_take(v_a_246_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
v_zetaDeltaFVarIds_267_ = lean_ctor_get(v___x_265_, 2);
v_postponed_268_ = lean_ctor_get(v___x_265_, 3);
v_diag_269_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_265_, 1);
lean_dec(v_unused_281_);
v___x_271_ = v___x_265_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_diag_269_);
lean_inc(v_postponed_268_);
lean_inc(v_zetaDeltaFVarIds_267_);
lean_inc(v_mctx_266_);
lean_dec(v___x_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_mctx_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_zetaDeltaFVarIds_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_postponed_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_diag_269_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_st_ref_put(v_a_246_, v___x_275_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
v___jp_282_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
v___jp_287_:
{
if (lean_obj_tag(v___y_288_) == 0)
{
lean_object* v_a_289_; uint8_t v___x_290_; 
v_a_289_ = lean_ctor_get(v___y_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___y_288_, 1);
v___x_290_ = lean_unbox(v_a_289_);
lean_dec(v_a_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v_env_292_; lean_object* v_nextMacroScope_293_; lean_object* v_ngen_294_; lean_object* v_auxDeclNGen_295_; lean_object* v_traceState_296_; lean_object* v_messages_297_; lean_object* v_infoState_298_; lean_object* v_snapshotTasks_299_; uint8_t v___x_300_; 
v___x_291_ = lean_st_ref_take(v_a_248_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
v_nextMacroScope_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_nextMacroScope_293_);
v_ngen_294_ = lean_ctor_get(v___x_291_, 2);
lean_inc_ref(v_ngen_294_);
v_auxDeclNGen_295_ = lean_ctor_get(v___x_291_, 3);
lean_inc_ref(v_auxDeclNGen_295_);
v_traceState_296_ = lean_ctor_get(v___x_291_, 4);
lean_inc_ref(v_traceState_296_);
v_messages_297_ = lean_ctor_get(v___x_291_, 6);
lean_inc_ref(v_messages_297_);
v_infoState_298_ = lean_ctor_get(v___x_291_, 7);
lean_inc_ref(v_infoState_298_);
v_snapshotTasks_299_ = lean_ctor_get(v___x_291_, 8);
lean_inc_ref(v_snapshotTasks_299_);
lean_dec(v___x_291_);
v___x_300_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
v_nextMacroScope_254_ = v_nextMacroScope_293_;
v_ngen_255_ = v_ngen_294_;
v_auxDeclNGen_256_ = v_auxDeclNGen_295_;
v_traceState_257_ = v_traceState_296_;
v_messages_258_ = v_messages_297_;
v_infoState_259_ = v_infoState_298_;
v_snapshotTasks_260_ = v_snapshotTasks_299_;
v___y_261_ = v_env_292_;
goto v___jp_253_;
}
else
{
size_t v_sz_301_; size_t v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_sz_301_ = lean_array_size(v_preDefs_241_);
v___x_302_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_241_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_301_, v___x_302_, v_preDefs_241_);
v___x_304_ = lean_nat_dec_le(v___x_286_, v___x_286_);
if (v___x_304_ == 0)
{
if (v___x_300_ == 0)
{
lean_dec_ref(v___x_303_);
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
v_nextMacroScope_254_ = v_nextMacroScope_293_;
v_ngen_255_ = v_ngen_294_;
v_auxDeclNGen_256_ = v_auxDeclNGen_295_;
v_traceState_257_ = v_traceState_296_;
v_messages_258_ = v_messages_297_;
v_infoState_259_ = v_infoState_298_;
v_snapshotTasks_260_ = v_snapshotTasks_299_;
v___y_261_ = v_env_292_;
goto v___jp_253_;
}
else
{
size_t v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_usize_of_nat(v___x_286_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_303_, v_declNameNonRec_242_, v_fixedParamPerms_243_, v_fixpointType_244_, v_preDefs_241_, v___x_302_, v___x_305_, v_env_292_);
lean_dec_ref(v_preDefs_241_);
v_nextMacroScope_254_ = v_nextMacroScope_293_;
v_ngen_255_ = v_ngen_294_;
v_auxDeclNGen_256_ = v_auxDeclNGen_295_;
v_traceState_257_ = v_traceState_296_;
v_messages_258_ = v_messages_297_;
v_infoState_259_ = v_infoState_298_;
v_snapshotTasks_260_ = v_snapshotTasks_299_;
v___y_261_ = v___x_306_;
goto v___jp_253_;
}
}
else
{
size_t v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_usize_of_nat(v___x_286_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_303_, v_declNameNonRec_242_, v_fixedParamPerms_243_, v_fixpointType_244_, v_preDefs_241_, v___x_302_, v___x_307_, v_env_292_);
lean_dec_ref(v_preDefs_241_);
v_nextMacroScope_254_ = v_nextMacroScope_293_;
v_ngen_255_ = v_ngen_294_;
v_auxDeclNGen_256_ = v_auxDeclNGen_295_;
v_traceState_257_ = v_traceState_296_;
v_messages_258_ = v_messages_297_;
v_infoState_259_ = v_infoState_298_;
v_snapshotTasks_260_ = v_snapshotTasks_299_;
v___y_261_ = v___x_308_;
goto v___jp_253_;
}
}
}
else
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
goto v___jp_250_;
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
v_a_309_ = lean_ctor_get(v___y_288_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___y_288_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___y_288_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___y_288_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
v___jp_317_:
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_318_ == 0)
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
goto v___jp_282_;
}
else
{
if (v___x_318_ == 0)
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
goto v___jp_282_;
}
else
{
size_t v___x_319_; size_t v___x_320_; uint8_t v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_286_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_241_, v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
goto v___jp_282_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = 0;
if (v___x_318_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_321_, v___x_322_, v___x_318_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
v___y_288_ = v___x_323_;
goto v___jp_287_;
}
else
{
if (v___x_318_ == 0)
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
goto v___jp_250_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_321_, v_preDefs_241_, v___x_319_, v___x_320_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; uint8_t v___x_326_; lean_object* v___x_327_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_unbox(v_a_325_);
lean_dec(v_a_325_);
v___x_327_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_321_, v___x_322_, v___x_326_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
v___y_288_ = v___x_327_;
goto v___jp_287_;
}
else
{
v___y_288_ = v___x_324_;
goto v___jp_287_;
}
}
}
}
}
}
}
v___jp_328_:
{
if (lean_obj_tag(v___y_329_) == 0)
{
lean_dec_ref_known(v___y_329_, 1);
goto v___jp_317_;
}
else
{
lean_dec_ref(v_fixpointType_244_);
lean_dec_ref(v_fixedParamPerms_243_);
lean_dec(v_declNameNonRec_242_);
lean_dec_ref(v_preDefs_241_);
return v___y_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_339_, lean_object* v_declNameNonRec_340_, lean_object* v_fixedParamPerms_341_, lean_object* v_fixpointType_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_339_, v_declNameNonRec_340_, v_fixedParamPerms_341_, v_fixpointType_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_349_, size_t v_i_350_, size_t v_stop_351_, lean_object* v_b_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_349_, v_i_350_, v_stop_351_, v_b_352_, v___y_355_, v___y_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_359_, lean_object* v_i_360_, lean_object* v_stop_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
size_t v_i_boxed_368_; size_t v_stop_boxed_369_; lean_object* v_res_370_; 
v_i_boxed_368_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_stop_boxed_369_ = lean_unbox_usize(v_stop_361_);
lean_dec(v_stop_361_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_359_, v_i_boxed_368_, v_stop_boxed_369_, v_b_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_as_359_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_a_387_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_378_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_378_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_395_, lean_object* v_x_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_395_, v_x_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_mvarId_404_, lean_object* v_x_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_404_, v_x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_412_, lean_object* v_mvarId_413_, lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_412_, v_mvarId_413_, v_x_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_421_, lean_object* v_declNameNonRec_422_, lean_object* v_n_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_name_eq(v_n_423_, v_declName_421_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; 
v___x_425_ = lean_name_eq(v_n_423_, v_declNameNonRec_422_);
return v___x_425_;
}
else
{
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_426_, lean_object* v_declNameNonRec_427_, lean_object* v_n_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_426_, v_declNameNonRec_427_, v_n_428_);
lean_dec(v_n_428_);
lean_dec(v_declNameNonRec_427_);
lean_dec(v_declName_426_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_441_ = l_Lean_MessageData_ofFormat(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_444_, lean_object* v___f_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc(v_mvarId_444_);
v___x_451_ = l_Lean_MVarId_getType_x27(v_mvarId_444_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_454_ = lean_unsigned_to_nat(3u);
v___x_455_ = l_Lean_Expr_isAppOfArity(v_a_452_, v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_a_452_);
lean_dec_ref(v___f_445_);
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_457_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_458_ = l_Lean_Meta_throwTacticEx___redArg(v___x_456_, v_mvarId_444_, v___x_457_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_Expr_appFn_x21(v_a_452_);
v___x_460_ = l_Lean_Expr_appArg_x21(v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = 0;
v___x_462_ = l_Lean_Meta_deltaExpand(v___x_460_, v___f_445_, v___x_461_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Expr_appArg_x21(v_a_452_);
lean_dec(v_a_452_);
v___x_465_ = l_Lean_Meta_mkEq(v_a_463_, v___x_464_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_444_, v_a_466_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v___x_467_;
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_mvarId_444_);
v_a_468_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_465_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_452_);
lean_dec(v_mvarId_444_);
v_a_476_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_462_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_462_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v___f_445_);
lean_dec(v_mvarId_444_);
v_a_484_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_451_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_451_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_492_, lean_object* v___f_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_492_, v___f_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_500_, lean_object* v_declNameNonRec_501_, lean_object* v_mvarId_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_508_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_508_, 0, v_declName_500_);
lean_closure_set(v___f_508_, 1, v_declNameNonRec_501_);
lean_inc(v_mvarId_502_);
v___f_509_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_509_, 0, v_mvarId_502_);
lean_closure_set(v___f_509_, 1, v___f_508_);
v___x_510_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_502_, v___f_509_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_511_, lean_object* v_declNameNonRec_512_, lean_object* v_mvarId_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_511_, v_declNameNonRec_512_, v_mvarId_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(lean_object* v_msg_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = l_Lean_instInhabitedExpr;
v___x_522_ = lean_panic_fn_borrowed(v___x_521_, v_msg_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(lean_object* v_msgData_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_env_530_; lean_object* v___x_531_; lean_object* v_mctx_532_; lean_object* v_lctx_533_; lean_object* v_options_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_env_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_env_530_);
lean_dec(v___x_529_);
v___x_531_ = lean_st_ref_get(v___y_525_);
v_mctx_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_mctx_532_);
lean_dec(v___x_531_);
v_lctx_533_ = lean_ctor_get(v___y_524_, 2);
v_options_534_ = lean_ctor_get(v___y_526_, 2);
lean_inc_ref(v_options_534_);
lean_inc_ref(v_lctx_533_);
v___x_535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_535_, 0, v_env_530_);
lean_ctor_set(v___x_535_, 1, v_mctx_532_);
lean_ctor_set(v___x_535_, 2, v_lctx_533_);
lean_ctor_set(v___x_535_, 3, v_options_534_);
v___x_536_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v_msgData_523_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(lean_object* v_msgData_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(lean_object* v_msg_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_ref_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_561_; 
v_ref_551_ = lean_ctor_get(v___y_548_, 5);
v___x_552_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_inc(v_ref_551_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_ref_551_);
lean_ctor_set(v___x_557_, 1, v_a_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 1);
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = l_Lean_Expr_bvar___override(v___x_589_);
return v___x_590_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12(void){
_start:
{
lean_object* v___x_591_; size_t v___x_592_; 
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_592_ = lean_ptr_addr(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15));
v___x_597_ = lean_unsigned_to_nat(18u);
v___x_598_ = lean_unsigned_to_nat(1896u);
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14));
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_601_ = l_mkPanicMessageWithDecl(v___x_600_, v___x_599_, v___x_598_, v___x_597_, v___x_596_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21(void){
_start:
{
lean_object* v___x_610_; lean_object* v_dummy_611_; 
v___x_610_ = lean_box(0);
v_dummy_611_ = l_Lean_Expr_sort___override(v___x_610_);
return v_dummy_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2));
v___x_624_ = lean_unsigned_to_nat(4u);
v___x_625_ = l_Lean_Expr_isAppOfArity(v_lhs_617_, v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4));
v___x_627_ = l_Lean_Expr_isAppOfArity(v_lhs_617_, v___x_626_, v___x_624_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = l_Lean_Expr_isApp(v_lhs_617_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_Expr_isProj(v_lhs_617_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_631_ = l_Lean_MessageData_ofExpr(v_lhs_617_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_632_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = l_Lean_Expr_projExpr_x21(v_lhs_617_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc_ref(v___x_634_);
v___x_635_ = lean_infer_type(v___x_634_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_634_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___y_642_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_640_ = 0;
if (lean_obj_tag(v_lhs_617_) == 11)
{
lean_object* v_typeName_650_; lean_object* v_idx_651_; lean_object* v_struct_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; uint8_t v___x_656_; 
v_typeName_650_ = lean_ctor_get(v_lhs_617_, 0);
v_idx_651_ = lean_ctor_get(v_lhs_617_, 1);
v_struct_652_ = lean_ctor_get(v_lhs_617_, 2);
v___x_653_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_654_ = lean_ptr_addr(v_struct_652_);
v___x_655_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
v___x_656_ = lean_usize_dec_eq(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_inc(v_idx_651_);
lean_inc(v_typeName_650_);
lean_dec_ref_known(v_lhs_617_, 3);
v___x_657_ = l_Lean_Expr_proj___override(v_typeName_650_, v_idx_651_, v___x_653_);
v___y_642_ = v___x_657_;
goto v___jp_641_;
}
else
{
v___y_642_ = v_lhs_617_;
goto v___jp_641_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec_ref(v_lhs_617_);
v___x_658_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
v___x_659_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_658_);
v___y_642_ = v___x_659_;
goto v___jp_641_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_643_ = l_Lean_mkLambda(v___x_639_, v___x_640_, v_a_636_, v___y_642_);
v___x_644_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
v___x_647_ = lean_array_push(v___x_646_, v___x_643_);
v___x_648_ = lean_array_push(v___x_647_, v_a_638_);
v___x_649_ = l_Lean_Meta_mkAppM(v___x_644_, v___x_648_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_649_;
}
}
else
{
lean_dec(v_a_636_);
lean_dec_ref(v_lhs_617_);
return v___x_637_;
}
}
else
{
lean_dec_ref(v___x_634_);
lean_dec_ref(v_lhs_617_);
return v___x_635_;
}
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = l_Lean_Expr_appFn_x21(v_lhs_617_);
v___x_661_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_660_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18));
v___x_664_ = l_Lean_Expr_appArg_x21(v_lhs_617_);
lean_dec_ref(v_lhs_617_);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_mk_empty_array_with_capacity(v___x_665_);
v___x_667_ = lean_array_push(v___x_666_, v_a_662_);
v___x_668_ = lean_array_push(v___x_667_, v___x_664_);
v___x_669_ = l_Lean_Meta_mkAppM(v___x_663_, v___x_668_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_669_;
}
else
{
lean_dec_ref(v_lhs_617_);
return v___x_661_;
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_dummy_674_; lean_object* v_nargs_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20));
v___x_671_ = l_Lean_Expr_getAppFn(v_lhs_617_);
v___x_672_ = l_Lean_Expr_constLevels_x21(v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = l_Lean_mkConst(v___x_670_, v___x_672_);
v_dummy_674_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_675_ = l_Lean_Expr_getAppNumArgs(v_lhs_617_);
lean_inc(v_nargs_675_);
v___x_676_ = lean_mk_array(v_nargs_675_, v_dummy_674_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_sub(v_nargs_675_, v___x_677_);
lean_dec(v_nargs_675_);
v___x_679_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_617_, v___x_676_, v___x_678_);
v___x_680_ = l_Lean_mkAppN(v___x_673_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_dummy_686_; lean_object* v_nargs_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23));
v___x_683_ = l_Lean_Expr_getAppFn(v_lhs_617_);
v___x_684_ = l_Lean_Expr_constLevels_x21(v___x_683_);
lean_dec_ref(v___x_683_);
v___x_685_ = l_Lean_mkConst(v___x_682_, v___x_684_);
v_dummy_686_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
v_nargs_687_ = l_Lean_Expr_getAppNumArgs(v_lhs_617_);
lean_inc(v_nargs_687_);
v___x_688_ = lean_mk_array(v_nargs_687_, v_dummy_686_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_sub(v_nargs_687_, v___x_689_);
lean_dec(v_nargs_687_);
v___x_691_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_617_, v___x_688_, v___x_690_);
v___x_692_ = l_Lean_mkAppN(v___x_685_, v___x_691_);
lean_dec_ref(v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_00_u03b1_701_, lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(lean_object* v_00_u03b1_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_709_, v_msg_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_1515__overap_725_; lean_object* v___x_726_; 
v___f_724_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1515__overap_725_ = lean_panic_fn_borrowed(v___f_724_, v_msg_718_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
v___x_726_ = lean_apply_5(v___x_1515__overap_725_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v_ks_738_; lean_object* v_vs_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_763_; 
v_ks_738_ = lean_ctor_get(v_x_734_, 0);
v_vs_739_ = lean_ctor_get(v_x_734_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_763_ == 0)
{
v___x_741_ = v_x_734_;
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_vs_739_);
lean_inc(v_ks_738_);
lean_dec(v_x_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_ks_738_);
v___x_744_ = lean_nat_dec_lt(v_x_735_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec(v_x_735_);
v___x_745_ = lean_array_push(v_ks_738_, v_x_736_);
v___x_746_ = lean_array_push(v_vs_739_, v_x_737_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_746_);
lean_ctor_set(v___x_741_, 0, v___x_745_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v_k_x27_750_; uint8_t v___x_751_; 
v_k_x27_750_ = lean_array_fget_borrowed(v_ks_738_, v_x_735_);
v___x_751_ = l_Lean_instBEqMVarId_beq(v_x_736_, v_k_x27_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_753_; 
if (v_isShared_742_ == 0)
{
v___x_753_ = v___x_741_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_ks_738_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_vs_739_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_x_735_, v___x_754_);
lean_dec(v_x_735_);
v_x_734_ = v___x_753_;
v_x_735_ = v___x_755_;
goto _start;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_array_fset(v_ks_738_, v_x_735_, v_x_736_);
v___x_759_ = lean_array_fset(v_vs_739_, v_x_735_, v_x_737_);
lean_dec(v_x_735_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_759_);
lean_ctor_set(v___x_741_, 0, v___x_758_);
v___x_761_ = v___x_741_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_764_, lean_object* v_k_765_, lean_object* v_v_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_764_, v___x_767_, v_k_765_, v_v_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_770_, size_t v_x_771_, size_t v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v_es_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_j_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_es_775_ = lean_ctor_get(v_x_770_, 0);
v___x_776_ = ((size_t)31ULL);
v___x_777_ = lean_usize_land(v_x_771_, v___x_776_);
v_j_778_ = lean_usize_to_nat(v___x_777_);
v___x_779_ = lean_array_get_size(v_es_775_);
v___x_780_ = lean_nat_dec_lt(v_j_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v_j_778_);
lean_dec(v_x_774_);
lean_dec(v_x_773_);
return v_x_770_;
}
else
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_819_; 
lean_inc_ref(v_es_775_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_x_770_, 0);
lean_dec(v_unused_820_);
v___x_782_ = v_x_770_;
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_x_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_v_784_; lean_object* v___x_785_; lean_object* v_xs_x27_786_; lean_object* v___y_788_; 
v_v_784_ = lean_array_fget(v_es_775_, v_j_778_);
v___x_785_ = lean_box(0);
v_xs_x27_786_ = lean_array_fset(v_es_775_, v_j_778_, v___x_785_);
switch(lean_obj_tag(v_v_784_))
{
case 0:
{
lean_object* v_key_793_; lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_key_793_ = lean_ctor_get(v_v_784_, 0);
v_val_794_ = lean_ctor_get(v_v_784_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_v_784_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v_v_784_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_inc(v_key_793_);
lean_dec(v_v_784_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
uint8_t v___x_798_; 
v___x_798_ = l_Lean_instBEqMVarId_beq(v_x_773_, v_key_793_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_796_);
v___x_799_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_793_, v_val_794_, v_x_773_, v_x_774_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
v___y_788_ = v___x_800_;
goto v___jp_787_;
}
else
{
lean_object* v___x_802_; 
lean_dec(v_val_794_);
lean_dec(v_key_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_x_774_);
lean_ctor_set(v___x_796_, 0, v_x_773_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_x_773_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_x_774_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_788_ = v___x_802_;
goto v___jp_787_;
}
}
}
}
case 1:
{
lean_object* v_node_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_817_; 
v_node_805_ = lean_ctor_get(v_v_784_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_v_784_);
if (v_isSharedCheck_817_ == 0)
{
v___x_807_ = v_v_784_;
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_node_805_);
lean_dec(v_v_784_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_809_ = ((size_t)5ULL);
v___x_810_ = lean_usize_shift_right(v_x_771_, v___x_809_);
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_add(v_x_772_, v___x_811_);
v___x_813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_805_, v___x_810_, v___x_812_, v_x_773_, v_x_774_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v___y_788_ = v___x_815_;
goto v___jp_787_;
}
}
}
default: 
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_x_773_);
lean_ctor_set(v___x_818_, 1, v_x_774_);
v___y_788_ = v___x_818_;
goto v___jp_787_;
}
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_array_fset(v_xs_x27_786_, v_j_778_, v___y_788_);
lean_dec(v_j_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_789_);
v___x_791_ = v___x_782_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
else
{
lean_object* v_ks_821_; lean_object* v_vs_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_840_; 
v_ks_821_ = lean_ctor_get(v_x_770_, 0);
v_vs_822_ = lean_ctor_get(v_x_770_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_840_ == 0)
{
v___x_824_ = v_x_770_;
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_vs_822_);
lean_inc(v_ks_821_);
lean_dec(v_x_770_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_821_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_822_);
v___x_827_ = v_reuseFailAlloc_839_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v_newNode_828_; size_t v___x_829_; uint8_t v___x_830_; 
v_newNode_828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_827_, v_x_773_, v_x_774_);
v___x_829_ = ((size_t)7ULL);
v___x_830_ = lean_usize_dec_le(v___x_829_, v_x_772_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_828_);
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_nat_dec_lt(v___x_831_, v___x_832_);
lean_dec(v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_ks_834_ = lean_ctor_get(v_newNode_828_, 0);
lean_inc_ref(v_ks_834_);
v_vs_835_ = lean_ctor_get(v_newNode_828_, 1);
lean_inc_ref(v_vs_835_);
lean_dec_ref(v_newNode_828_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_772_, v_ks_834_, v_vs_835_, v___x_836_, v___x_837_);
lean_dec_ref(v_vs_835_);
lean_dec_ref(v_ks_834_);
return v___x_838_;
}
else
{
return v_newNode_828_;
}
}
else
{
return v_newNode_828_;
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
size_t v_x_2098__boxed_873_; size_t v_x_2099__boxed_874_; lean_object* v_res_875_; 
v_x_2098__boxed_873_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_x_2099__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_res_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_868_, v_x_2098__boxed_873_, v_x_2099__boxed_874_, v_x_871_, v_x_872_);
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
lean_object* v___x_887_; lean_object* v_mctx_888_; lean_object* v_cache_889_; lean_object* v_zetaDeltaFVarIds_890_; lean_object* v_postponed_891_; lean_object* v_diag_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_921_; 
v___x_887_ = lean_st_ref_take(v___y_885_);
v_mctx_888_ = lean_ctor_get(v___x_887_, 0);
v_cache_889_ = lean_ctor_get(v___x_887_, 1);
v_zetaDeltaFVarIds_890_ = lean_ctor_get(v___x_887_, 2);
v_postponed_891_ = lean_ctor_get(v___x_887_, 3);
v_diag_892_ = lean_ctor_get(v___x_887_, 4);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_921_ == 0)
{
v___x_894_ = v___x_887_;
v_isShared_895_ = v_isSharedCheck_921_;
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
v_isShared_895_ = v_isSharedCheck_921_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_depth_896_; lean_object* v_levelAssignDepth_897_; lean_object* v_lmvarCounter_898_; lean_object* v_mvarCounter_899_; lean_object* v_lDecls_900_; lean_object* v_decls_901_; lean_object* v_userNames_902_; lean_object* v_lAssignment_903_; lean_object* v_eAssignment_904_; lean_object* v_dAssignment_905_; lean_object* v_instanceTypedMVars_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
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
v_instanceTypedMVars_906_ = lean_ctor_get(v_mctx_888_, 10);
v_isSharedCheck_920_ = !lean_is_exclusive(v_mctx_888_);
if (v_isSharedCheck_920_ == 0)
{
v___x_908_ = v_mctx_888_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_instanceTypedMVars_906_);
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
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_904_, v_mvarId_883_, v_val_884_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 8, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_depth_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_levelAssignDepth_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_lmvarCounter_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_mvarCounter_899_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_lDecls_900_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_decls_901_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_userNames_902_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_lAssignment_903_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_dAssignment_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 10, v_instanceTypedMVars_906_);
v___x_912_ = v_reuseFailAlloc_919_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_912_);
v___x_914_ = v___x_894_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_cache_889_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_zetaDeltaFVarIds_890_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_postponed_891_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_diag_892_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_st_ref_put(v___y_885_, v___x_914_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_922_, lean_object* v_val_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_922_, v_val_923_, v___y_924_);
lean_dec(v___y_924_);
return v_res_926_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_931_ = lean_unsigned_to_nat(41u);
v___x_932_ = lean_unsigned_to_nat(70u);
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_935_ = l_mkPanicMessageWithDecl(v___x_934_, v___x_933_, v___x_932_, v___x_931_, v___x_930_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_937_ = lean_unsigned_to_nat(51u);
v___x_938_ = lean_unsigned_to_nat(72u);
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_941_ = l_mkPanicMessageWithDecl(v___x_940_, v___x_939_, v___x_938_, v___x_937_, v___x_936_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
lean_inc(v_mvarId_942_);
v___x_948_ = l_Lean_MVarId_getType_x27(v_mvarId_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_951_ = lean_unsigned_to_nat(3u);
v___x_952_ = l_Lean_Expr_isAppOfArity(v_a_949_, v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_a_949_);
lean_dec(v_mvarId_942_);
v___x_953_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_954_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_953_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = l_Lean_Expr_appFn_x21(v_a_949_);
v___x_956_ = l_Lean_Expr_appArg_x21(v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_956_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_n(v_a_958_, 2);
lean_dec_ref_known(v___x_957_, 1);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
v___x_959_ = lean_infer_type(v_a_958_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = l_Lean_Expr_isAppOfArity(v_a_960_, v___x_950_, v___x_951_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_a_960_);
lean_dec(v_a_958_);
lean_dec(v_a_949_);
lean_dec(v_mvarId_942_);
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_963_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_962_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = l_Lean_Expr_appArg_x21(v_a_949_);
lean_dec(v_a_949_);
v___x_965_ = l_Lean_Expr_appArg_x21(v_a_960_);
lean_dec(v_a_960_);
v___x_966_ = l_Lean_Meta_mkEq(v___x_965_, v___x_964_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_967_, v___x_968_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_n(v_a_970_, 2);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Meta_mkEqTrans(v_a_958_, v_a_970_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v___y_943_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_942_, v_a_972_, v___y_944_);
lean_dec(v___y_944_);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_982_);
v___x_975_ = v___x_973_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_973_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Expr_mvarId_x21(v_a_970_);
lean_dec(v_a_970_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_970_);
lean_dec(v___y_944_);
lean_dec(v_mvarId_942_);
v_a_983_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_971_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_971_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_958_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_mvarId_942_);
v_a_991_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_969_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_969_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_a_958_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_mvarId_942_);
v_a_999_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_966_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_966_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_958_);
lean_dec(v_a_949_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_mvarId_942_);
v_a_1007_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_959_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_959_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_949_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_mvarId_942_);
v_a_1015_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_957_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_957_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_mvarId_942_);
v_a_1023_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_948_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_948_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; 
lean_inc(v_mvarId_1038_);
v___f_1044_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1044_, 0, v_mvarId_1038_);
v___x_1045_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1038_, v___f_1044_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1053_, lean_object* v_val_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1053_, v_val_1054_, v___y_1056_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1061_, lean_object* v_val_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1061_, v_val_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1070_, v_x_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, size_t v_x_1076_, size_t v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1075_, v_x_1076_, v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
size_t v_x_2574__boxed_1087_; size_t v_x_2575__boxed_1088_; lean_object* v_res_1089_; 
v_x_2574__boxed_1087_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_x_2575__boxed_1088_ = lean_unbox_usize(v_x_1084_);
lean_dec(v_x_1084_);
v_res_1089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1081_, v_x_1082_, v_x_2574__boxed_1087_, v_x_2575__boxed_1088_, v_x_1085_, v_x_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1090_, lean_object* v_n_1091_, lean_object* v_k_1092_, lean_object* v_v_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1091_, v_k_1092_, v_v_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1095_, size_t v_depth_1096_, lean_object* v_keys_1097_, lean_object* v_vals_1098_, lean_object* v_heq_1099_, lean_object* v_i_1100_, lean_object* v_entries_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1096_, v_keys_1097_, v_vals_1098_, v_i_1100_, v_entries_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1103_, lean_object* v_depth_1104_, lean_object* v_keys_1105_, lean_object* v_vals_1106_, lean_object* v_heq_1107_, lean_object* v_i_1108_, lean_object* v_entries_1109_){
_start:
{
size_t v_depth_boxed_1110_; lean_object* v_res_1111_; 
v_depth_boxed_1110_ = lean_unbox_usize(v_depth_1104_);
lean_dec(v_depth_1104_);
v_res_1111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1103_, v_depth_boxed_1110_, v_keys_1105_, v_vals_1106_, v_heq_1107_, v_i_1108_, v_entries_1109_);
lean_dec_ref(v_vals_1106_);
lean_dec_ref(v_keys_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1113_, v_x_1114_, v_x_1115_, v_x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1118_, lean_object* v_opt_1119_){
_start:
{
lean_object* v_name_1120_; lean_object* v_defValue_1121_; lean_object* v_map_1122_; lean_object* v___x_1123_; 
v_name_1120_ = lean_ctor_get(v_opt_1119_, 0);
v_defValue_1121_ = lean_ctor_get(v_opt_1119_, 1);
v_map_1122_ = lean_ctor_get(v_opts_1118_, 0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1122_, v_name_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_unbox(v_defValue_1121_);
return v___x_1124_;
}
else
{
lean_object* v_val_1125_; 
v_val_1125_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v___x_1123_, 1);
if (lean_obj_tag(v_val_1125_) == 1)
{
uint8_t v_v_1126_; 
v_v_1126_ = lean_ctor_get_uint8(v_val_1125_, 0);
lean_dec_ref_known(v_val_1125_, 0);
return v_v_1126_;
}
else
{
uint8_t v___x_1127_; 
lean_dec(v_val_1125_);
v___x_1127_ = lean_unbox(v_defValue_1121_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1128_, lean_object* v_opt_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1128_, v_opt_1129_);
lean_dec_ref(v_opt_1129_);
lean_dec_ref(v_opts_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1132_, lean_object* v_opt_1133_){
_start:
{
lean_object* v_name_1134_; lean_object* v_defValue_1135_; lean_object* v_map_1136_; lean_object* v___x_1137_; 
v_name_1134_ = lean_ctor_get(v_opt_1133_, 0);
v_defValue_1135_ = lean_ctor_get(v_opt_1133_, 1);
v_map_1136_ = lean_ctor_get(v_opts_1132_, 0);
v___x_1137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1136_, v_name_1134_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_inc(v_defValue_1135_);
return v_defValue_1135_;
}
else
{
lean_object* v_val_1138_; 
v_val_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v___x_1137_, 1);
if (lean_obj_tag(v_val_1138_) == 3)
{
lean_object* v_v_1139_; 
v_v_1139_ = lean_ctor_get(v_val_1138_, 0);
lean_inc(v_v_1139_);
lean_dec_ref_known(v_val_1138_, 1);
return v_v_1139_;
}
else
{
lean_dec(v_val_1138_);
lean_inc(v_defValue_1135_);
return v_defValue_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1140_, lean_object* v_opt_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1140_, v_opt_1141_);
lean_dec_ref(v_opt_1141_);
lean_dec_ref(v_opts_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_e_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_Expr_hasMVar(v_e_1143_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_e_1143_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v_mctx_1149_; lean_object* v___x_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1153_; lean_object* v_cache_1154_; lean_object* v_zetaDeltaFVarIds_1155_; lean_object* v_postponed_1156_; lean_object* v_diag_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1166_; 
v___x_1148_ = lean_st_ref_get(v___y_1144_);
v_mctx_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_mctx_1149_);
lean_dec(v___x_1148_);
v___x_1150_ = l_Lean_instantiateMVarsCore(v_mctx_1149_, v_e_1143_);
v_fst_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_fst_1151_);
v_snd_1152_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v___x_1150_);
v___x_1153_ = lean_st_ref_take(v___y_1144_);
v_cache_1154_ = lean_ctor_get(v___x_1153_, 1);
v_zetaDeltaFVarIds_1155_ = lean_ctor_get(v___x_1153_, 2);
v_postponed_1156_ = lean_ctor_get(v___x_1153_, 3);
v_diag_1157_ = lean_ctor_get(v___x_1153_, 4);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1167_);
v___x_1159_ = v___x_1153_;
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_diag_1157_);
lean_inc(v_postponed_1156_);
lean_inc(v_zetaDeltaFVarIds_1155_);
lean_inc(v_cache_1154_);
lean_dec(v___x_1153_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_snd_1152_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_snd_1152_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_cache_1154_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_zetaDeltaFVarIds_1155_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_postponed_1156_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_diag_1157_);
v___x_1162_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_st_ref_put(v___y_1144_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_fst_1151_);
return v___x_1164_;
}
}
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
v___x_1429_ = lean_st_ref_put(v___y_1390_, v___x_1428_);
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
lean_object* v___y_1503_; lean_object* v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v_fileName_1514_; lean_object* v_fileMap_1515_; lean_object* v_currRecDepth_1516_; lean_object* v_ref_1517_; lean_object* v_currNamespace_1518_; lean_object* v_openDecls_1519_; lean_object* v_initHeartbeats_1520_; lean_object* v_maxHeartbeats_1521_; lean_object* v_quotContext_1522_; lean_object* v_currMacroScope_1523_; lean_object* v_cancelTk_x3f_1524_; uint8_t v_suppressElabErrors_1525_; lean_object* v_inheritedTraceOptions_1526_; lean_object* v___y_1527_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1596_; lean_object* v___y_1618_; lean_object* v___y_1619_; uint8_t v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; uint8_t v___y_1624_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___x_1671_; 
v___x_1671_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1490_, v_declNameNonRec_1491_, v___x_1492_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___x_1711_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
lean_inc_ref(v___f_1493_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
v___x_1711_ = lean_apply_5(v___f_1493_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, lean_box(0));
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; uint8_t v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1713_ = lean_unbox(v_a_1712_);
lean_dec(v_a_1712_);
if (v___x_1713_ == 0)
{
v___y_1674_ = v___y_1497_;
v___y_1675_ = v___y_1498_;
v___y_1676_ = v___y_1499_;
v___y_1677_ = v___y_1500_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1714_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
lean_inc(v_a_1672_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_a_1672_);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
lean_inc(v___x_1495_);
v___x_1717_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1716_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_dec_ref_known(v___x_1717_, 1);
v___y_1674_ = v___y_1497_;
v___y_1675_ = v___y_1498_;
v___y_1676_ = v___y_1499_;
v___y_1677_ = v___y_1500_;
goto v___jp_1673_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1672_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1672_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1726_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1711_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1711_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
v___jp_1673_:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1672_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
v___x_1680_ = lean_apply_5(v___f_1493_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; uint8_t v___x_1682_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
if (v___x_1682_ == 0)
{
v___y_1661_ = v_a_1679_;
v___y_1662_ = v___y_1674_;
v___y_1663_ = v___y_1675_;
v___y_1664_ = v___y_1676_;
v___y_1665_ = v___y_1677_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
lean_inc(v_a_1679_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_a_1679_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
lean_inc(v___x_1495_);
v___x_1686_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1685_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_dec_ref_known(v___x_1686_, 1);
v___y_1661_ = v_a_1679_;
v___y_1662_ = v___y_1674_;
v___y_1663_ = v___y_1675_;
v___y_1664_ = v___y_1676_;
v___y_1665_ = v___y_1677_;
goto v___jp_1660_;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_a_1679_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1679_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1695_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1680_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1680_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1703_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1678_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1678_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v___f_1493_);
v_a_1734_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1671_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1671_);
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
v___jp_1502_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = l_Lean_maxRecDepth;
v___x_1529_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_1512_, v___x_1528_);
lean_inc_ref(v_inheritedTraceOptions_1526_);
lean_inc(v_cancelTk_x3f_1524_);
lean_inc(v_currMacroScope_1523_);
lean_inc(v_quotContext_1522_);
lean_inc(v_maxHeartbeats_1521_);
lean_inc(v_initHeartbeats_1520_);
lean_inc(v_openDecls_1519_);
lean_inc(v_currNamespace_1518_);
lean_inc(v_ref_1517_);
lean_inc(v_currRecDepth_1516_);
lean_inc_ref(v_fileMap_1515_);
lean_inc_ref(v_fileName_1514_);
v___x_1530_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1530_, 0, v_fileName_1514_);
lean_ctor_set(v___x_1530_, 1, v_fileMap_1515_);
lean_ctor_set(v___x_1530_, 2, v___y_1512_);
lean_ctor_set(v___x_1530_, 3, v_currRecDepth_1516_);
lean_ctor_set(v___x_1530_, 4, v___x_1529_);
lean_ctor_set(v___x_1530_, 5, v_ref_1517_);
lean_ctor_set(v___x_1530_, 6, v_currNamespace_1518_);
lean_ctor_set(v___x_1530_, 7, v_openDecls_1519_);
lean_ctor_set(v___x_1530_, 8, v_initHeartbeats_1520_);
lean_ctor_set(v___x_1530_, 9, v_maxHeartbeats_1521_);
lean_ctor_set(v___x_1530_, 10, v_quotContext_1522_);
lean_ctor_set(v___x_1530_, 11, v_currMacroScope_1523_);
lean_ctor_set(v___x_1530_, 12, v_cancelTk_x3f_1524_);
lean_ctor_set(v___x_1530_, 13, v_inheritedTraceOptions_1526_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*14, v___y_1505_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*14 + 1, v_suppressElabErrors_1525_);
v___x_1531_ = l_Lean_MVarId_refl(v___y_1504_, v___y_1507_, v___y_1503_, v___y_1508_, v___x_1530_, v___y_1527_);
lean_dec_ref_known(v___x_1530_, 14);
lean_dec_ref(v___y_1503_);
if (lean_obj_tag(v___x_1531_) == 0)
{
uint8_t v_hasTrace_1532_; 
lean_dec_ref_known(v___x_1531_, 1);
v_hasTrace_1532_ = lean_ctor_get_uint8(v___y_1511_, sizeof(void*)*1);
if (v_hasTrace_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref(v___y_1511_);
lean_dec(v___x_1495_);
v___x_1533_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_1495_);
v___x_1535_ = l_Lean_Name_append(v___x_1534_, v___x_1495_);
v___x_1536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1510_, v___y_1511_, v___x_1535_);
lean_dec(v___x_1535_);
lean_dec_ref(v___y_1511_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v___x_1495_);
v___x_1537_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1539_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1495_, v___x_1538_, v___y_1513_, v___y_1508_, v___y_1506_, v___y_1509_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref_known(v___x_1539_, 1);
v___x_1540_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1494_, v___y_1508_);
return v___x_1540_;
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_a_1494_);
v_a_1541_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1539_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1539_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v___y_1511_);
lean_dec(v___x_1495_);
lean_dec_ref(v_a_1494_);
v_a_1549_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1531_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1531_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
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
v___jp_1557_:
{
lean_object* v_fileName_1571_; lean_object* v_fileMap_1572_; lean_object* v_currRecDepth_1573_; lean_object* v_ref_1574_; lean_object* v_currNamespace_1575_; lean_object* v_openDecls_1576_; lean_object* v_initHeartbeats_1577_; lean_object* v_maxHeartbeats_1578_; lean_object* v_quotContext_1579_; lean_object* v_currMacroScope_1580_; lean_object* v_cancelTk_x3f_1581_; uint8_t v_suppressElabErrors_1582_; lean_object* v_inheritedTraceOptions_1583_; 
v_fileName_1571_ = lean_ctor_get(v___y_1569_, 0);
v_fileMap_1572_ = lean_ctor_get(v___y_1569_, 1);
v_currRecDepth_1573_ = lean_ctor_get(v___y_1569_, 3);
v_ref_1574_ = lean_ctor_get(v___y_1569_, 5);
v_currNamespace_1575_ = lean_ctor_get(v___y_1569_, 6);
v_openDecls_1576_ = lean_ctor_get(v___y_1569_, 7);
v_initHeartbeats_1577_ = lean_ctor_get(v___y_1569_, 8);
v_maxHeartbeats_1578_ = lean_ctor_get(v___y_1569_, 9);
v_quotContext_1579_ = lean_ctor_get(v___y_1569_, 10);
v_currMacroScope_1580_ = lean_ctor_get(v___y_1569_, 11);
v_cancelTk_x3f_1581_ = lean_ctor_get(v___y_1569_, 12);
v_suppressElabErrors_1582_ = lean_ctor_get_uint8(v___y_1569_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1583_ = lean_ctor_get(v___y_1569_, 13);
v___y_1503_ = v___y_1558_;
v___y_1504_ = v___y_1559_;
v___y_1505_ = v___y_1560_;
v___y_1506_ = v___y_1561_;
v___y_1507_ = v___y_1562_;
v___y_1508_ = v___y_1563_;
v___y_1509_ = v___y_1564_;
v___y_1510_ = v___y_1565_;
v___y_1511_ = v___y_1566_;
v___y_1512_ = v___y_1567_;
v___y_1513_ = v___y_1568_;
v_fileName_1514_ = v_fileName_1571_;
v_fileMap_1515_ = v_fileMap_1572_;
v_currRecDepth_1516_ = v_currRecDepth_1573_;
v_ref_1517_ = v_ref_1574_;
v_currNamespace_1518_ = v_currNamespace_1575_;
v_openDecls_1519_ = v_openDecls_1576_;
v_initHeartbeats_1520_ = v_initHeartbeats_1577_;
v_maxHeartbeats_1521_ = v_maxHeartbeats_1578_;
v_quotContext_1522_ = v_quotContext_1579_;
v_currMacroScope_1523_ = v_currMacroScope_1580_;
v_cancelTk_x3f_1524_ = v_cancelTk_x3f_1581_;
v_suppressElabErrors_1525_ = v_suppressElabErrors_1582_;
v_inheritedTraceOptions_1526_ = v_inheritedTraceOptions_1583_;
v___y_1527_ = v___y_1570_;
goto v___jp_1502_;
}
v___jp_1584_:
{
if (v___y_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v_env_1598_; lean_object* v_nextMacroScope_1599_; lean_object* v_ngen_1600_; lean_object* v_auxDeclNGen_1601_; lean_object* v_traceState_1602_; lean_object* v_messages_1603_; lean_object* v_infoState_1604_; lean_object* v_snapshotTasks_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1615_; 
v___x_1597_ = lean_st_ref_take(v___y_1591_);
v_env_1598_ = lean_ctor_get(v___x_1597_, 0);
v_nextMacroScope_1599_ = lean_ctor_get(v___x_1597_, 1);
v_ngen_1600_ = lean_ctor_get(v___x_1597_, 2);
v_auxDeclNGen_1601_ = lean_ctor_get(v___x_1597_, 3);
v_traceState_1602_ = lean_ctor_get(v___x_1597_, 4);
v_messages_1603_ = lean_ctor_get(v___x_1597_, 6);
v_infoState_1604_ = lean_ctor_get(v___x_1597_, 7);
v_snapshotTasks_1605_ = lean_ctor_get(v___x_1597_, 8);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1597_, 5);
lean_dec(v_unused_1616_);
v___x_1607_ = v___x_1597_;
v_isShared_1608_ = v_isSharedCheck_1615_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snapshotTasks_1605_);
lean_inc(v_infoState_1604_);
lean_inc(v_messages_1603_);
lean_inc(v_traceState_1602_);
lean_inc(v_auxDeclNGen_1601_);
lean_inc(v_ngen_1600_);
lean_inc(v_nextMacroScope_1599_);
lean_inc(v_env_1598_);
lean_dec(v___x_1597_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1615_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = l_Lean_Kernel_enableDiag(v_env_1598_, v___y_1587_);
v___x_1610_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 5, v___x_1610_);
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1599_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1600_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_traceState_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_messages_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_infoState_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_snapshotTasks_1605_);
v___x_1612_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_st_ref_put(v___y_1591_, v___x_1612_);
v___y_1558_ = v___y_1586_;
v___y_1559_ = v___y_1585_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1588_;
v___y_1562_ = v___y_1589_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1593_;
v___y_1566_ = v___y_1592_;
v___y_1567_ = v___y_1594_;
v___y_1568_ = v___y_1595_;
v___y_1569_ = v___y_1588_;
v___y_1570_ = v___y_1591_;
goto v___jp_1557_;
}
}
}
else
{
v___y_1558_ = v___y_1586_;
v___y_1559_ = v___y_1585_;
v___y_1560_ = v___y_1587_;
v___y_1561_ = v___y_1588_;
v___y_1562_ = v___y_1589_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1593_;
v___y_1566_ = v___y_1592_;
v___y_1567_ = v___y_1594_;
v___y_1568_ = v___y_1595_;
v___y_1569_ = v___y_1588_;
v___y_1570_ = v___y_1591_;
goto v___jp_1557_;
}
}
v___jp_1617_:
{
lean_object* v___x_1625_; lean_object* v_keyedConfig_1626_; uint8_t v_trackZetaDelta_1627_; lean_object* v_zetaDeltaSet_1628_; lean_object* v_lctx_1629_; lean_object* v_localInstances_1630_; lean_object* v_defEqCtx_x3f_1631_; lean_object* v_synthPendingDepth_1632_; lean_object* v_customCanUnfoldPredicate_x3f_1633_; uint8_t v_univApprox_1634_; uint8_t v_inTypeClassResolution_1635_; uint8_t v_cacheInferType_1636_; lean_object* v_fileName_1637_; lean_object* v_fileMap_1638_; lean_object* v_options_1639_; lean_object* v_currRecDepth_1640_; lean_object* v_ref_1641_; lean_object* v_currNamespace_1642_; lean_object* v_openDecls_1643_; lean_object* v_initHeartbeats_1644_; lean_object* v_maxHeartbeats_1645_; lean_object* v_quotContext_1646_; lean_object* v_currMacroScope_1647_; lean_object* v_cancelTk_x3f_1648_; uint8_t v_suppressElabErrors_1649_; lean_object* v_inheritedTraceOptions_1650_; lean_object* v_env_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1625_ = lean_st_ref_get(v___y_1622_);
v_keyedConfig_1626_ = lean_ctor_get(v___y_1623_, 0);
v_trackZetaDelta_1627_ = lean_ctor_get_uint8(v___y_1623_, sizeof(void*)*7);
v_zetaDeltaSet_1628_ = lean_ctor_get(v___y_1623_, 1);
v_lctx_1629_ = lean_ctor_get(v___y_1623_, 2);
v_localInstances_1630_ = lean_ctor_get(v___y_1623_, 3);
v_defEqCtx_x3f_1631_ = lean_ctor_get(v___y_1623_, 4);
v_synthPendingDepth_1632_ = lean_ctor_get(v___y_1623_, 5);
v_customCanUnfoldPredicate_x3f_1633_ = lean_ctor_get(v___y_1623_, 6);
v_univApprox_1634_ = lean_ctor_get_uint8(v___y_1623_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1635_ = lean_ctor_get_uint8(v___y_1623_, sizeof(void*)*7 + 2);
v_cacheInferType_1636_ = lean_ctor_get_uint8(v___y_1623_, sizeof(void*)*7 + 3);
v_fileName_1637_ = lean_ctor_get(v___y_1619_, 0);
v_fileMap_1638_ = lean_ctor_get(v___y_1619_, 1);
v_options_1639_ = lean_ctor_get(v___y_1619_, 2);
v_currRecDepth_1640_ = lean_ctor_get(v___y_1619_, 3);
v_ref_1641_ = lean_ctor_get(v___y_1619_, 5);
v_currNamespace_1642_ = lean_ctor_get(v___y_1619_, 6);
v_openDecls_1643_ = lean_ctor_get(v___y_1619_, 7);
v_initHeartbeats_1644_ = lean_ctor_get(v___y_1619_, 8);
v_maxHeartbeats_1645_ = lean_ctor_get(v___y_1619_, 9);
v_quotContext_1646_ = lean_ctor_get(v___y_1619_, 10);
v_currMacroScope_1647_ = lean_ctor_get(v___y_1619_, 11);
v_cancelTk_x3f_1648_ = lean_ctor_get(v___y_1619_, 12);
v_suppressElabErrors_1649_ = lean_ctor_get_uint8(v___y_1619_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1650_ = lean_ctor_get(v___y_1619_, 13);
v_env_1651_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_ref(v_env_1651_);
lean_dec(v___x_1625_);
lean_inc_ref(v_keyedConfig_1626_);
v___x_1652_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_1624_, v_keyedConfig_1626_);
lean_inc(v_customCanUnfoldPredicate_x3f_1633_);
lean_inc(v_synthPendingDepth_1632_);
lean_inc(v_defEqCtx_x3f_1631_);
lean_inc_ref(v_localInstances_1630_);
lean_inc_ref(v_lctx_1629_);
lean_inc(v_zetaDeltaSet_1628_);
v___x_1653_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v_zetaDeltaSet_1628_);
lean_ctor_set(v___x_1653_, 2, v_lctx_1629_);
lean_ctor_set(v___x_1653_, 3, v_localInstances_1630_);
lean_ctor_set(v___x_1653_, 4, v_defEqCtx_x3f_1631_);
lean_ctor_set(v___x_1653_, 5, v_synthPendingDepth_1632_);
lean_ctor_set(v___x_1653_, 6, v_customCanUnfoldPredicate_x3f_1633_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*7, v_trackZetaDelta_1627_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*7 + 1, v_univApprox_1634_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1635_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*7 + 3, v_cacheInferType_1636_);
v___x_1654_ = l_Lean_Meta_smartUnfolding;
v___x_1655_ = 0;
lean_inc_ref(v_options_1639_);
v___x_1656_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1639_, v___x_1654_, v___x_1655_);
v___x_1657_ = l_Lean_diagnostics;
v___x_1658_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1656_, v___x_1657_);
v___x_1659_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1651_);
lean_dec_ref(v_env_1651_);
if (v___x_1658_ == 0)
{
if (v___x_1659_ == 0)
{
lean_inc_ref(v_options_1639_);
v___y_1503_ = v___x_1653_;
v___y_1504_ = v___y_1618_;
v___y_1505_ = v___x_1658_;
v___y_1506_ = v___y_1619_;
v___y_1507_ = v___y_1620_;
v___y_1508_ = v___y_1621_;
v___y_1509_ = v___y_1622_;
v___y_1510_ = v_inheritedTraceOptions_1650_;
v___y_1511_ = v_options_1639_;
v___y_1512_ = v___x_1656_;
v___y_1513_ = v___y_1623_;
v_fileName_1514_ = v_fileName_1637_;
v_fileMap_1515_ = v_fileMap_1638_;
v_currRecDepth_1516_ = v_currRecDepth_1640_;
v_ref_1517_ = v_ref_1641_;
v_currNamespace_1518_ = v_currNamespace_1642_;
v_openDecls_1519_ = v_openDecls_1643_;
v_initHeartbeats_1520_ = v_initHeartbeats_1644_;
v_maxHeartbeats_1521_ = v_maxHeartbeats_1645_;
v_quotContext_1522_ = v_quotContext_1646_;
v_currMacroScope_1523_ = v_currMacroScope_1647_;
v_cancelTk_x3f_1524_ = v_cancelTk_x3f_1648_;
v_suppressElabErrors_1525_ = v_suppressElabErrors_1649_;
v_inheritedTraceOptions_1526_ = v_inheritedTraceOptions_1650_;
v___y_1527_ = v___y_1622_;
goto v___jp_1502_;
}
else
{
lean_inc_ref(v_options_1639_);
v___y_1585_ = v___y_1618_;
v___y_1586_ = v___x_1653_;
v___y_1587_ = v___x_1658_;
v___y_1588_ = v___y_1619_;
v___y_1589_ = v___y_1620_;
v___y_1590_ = v___y_1621_;
v___y_1591_ = v___y_1622_;
v___y_1592_ = v_options_1639_;
v___y_1593_ = v_inheritedTraceOptions_1650_;
v___y_1594_ = v___x_1656_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___x_1658_;
goto v___jp_1584_;
}
}
else
{
lean_inc_ref(v_options_1639_);
v___y_1585_ = v___y_1618_;
v___y_1586_ = v___x_1653_;
v___y_1587_ = v___x_1658_;
v___y_1588_ = v___y_1619_;
v___y_1589_ = v___y_1620_;
v___y_1590_ = v___y_1621_;
v___y_1591_ = v___y_1622_;
v___y_1592_ = v_options_1639_;
v___y_1593_ = v_inheritedTraceOptions_1650_;
v___y_1594_ = v___x_1656_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___x_1659_;
goto v___jp_1584_;
}
}
v___jp_1660_:
{
lean_object* v___x_1666_; uint8_t v_transparency_1667_; uint8_t v___x_1668_; uint8_t v___x_1669_; uint8_t v___x_1670_; 
v___x_1666_ = l_Lean_Meta_Context_config(v___y_1662_);
v_transparency_1667_ = lean_ctor_get_uint8(v___x_1666_, 9);
lean_dec_ref(v___x_1666_);
v___x_1668_ = 0;
v___x_1669_ = 1;
v___x_1670_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1667_, v___x_1668_);
if (v___x_1670_ == 0)
{
v___y_1618_ = v___y_1661_;
v___y_1619_ = v___y_1664_;
v___y_1620_ = v___x_1669_;
v___y_1621_ = v___y_1663_;
v___y_1622_ = v___y_1665_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v_transparency_1667_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___y_1661_;
v___y_1619_ = v___y_1664_;
v___y_1620_ = v___x_1669_;
v___y_1621_ = v___y_1663_;
v___y_1622_ = v___y_1665_;
v___y_1623_ = v___y_1662_;
v___y_1624_ = v___x_1668_;
goto v___jp_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1742_, lean_object* v_declNameNonRec_1743_, lean_object* v___x_1744_, lean_object* v___f_1745_, lean_object* v_a_1746_, lean_object* v___x_1747_, lean_object* v_____r_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1742_, v_declNameNonRec_1743_, v___x_1744_, v___f_1745_, v_a_1746_, v___x_1747_, v_____r_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1754_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_declName_1772_, lean_object* v_a_1773_, lean_object* v___x_1774_, lean_object* v_declNameNonRec_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1794_; lean_object* v_a_1795_; lean_object* v___y_1799_; lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1773_, v___x_1774_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1830_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6));
v___f_1804_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7));
v___x_1805_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1803_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = l_Lean_Expr_mvarId_x21(v_a_1802_);
v___x_1811_ = lean_unbox(v_a_1806_);
lean_dec(v_a_1806_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_del_object(v___x_1808_);
v___x_1812_ = lean_box(0);
lean_inc(v_declName_1772_);
v___x_1813_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1772_, v_declNameNonRec_1775_, v___x_1810_, v___f_1804_, v_a_1802_, v___x_1803_, v___x_1812_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
v___y_1799_ = v___x_1813_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
lean_inc(v___x_1810_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1816_ = v___x_1808_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1810_);
v___x_1816_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1814_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1803_, v___x_1817_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
lean_inc(v_declName_1772_);
v___x_1820_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1772_, v_declNameNonRec_1775_, v___x_1810_, v___f_1804_, v_a_1802_, v___x_1803_, v_a_1819_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
v___y_1799_ = v___x_1820_;
goto v___jp_1798_;
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v___x_1810_);
lean_dec(v_a_1802_);
lean_dec(v_declNameNonRec_1775_);
v_a_1821_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1818_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1818_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
lean_inc(v_a_1821_);
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1794_ = v___x_1826_;
v_a_1795_ = v_a_1821_;
goto v___jp_1793_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1775_);
v___y_1799_ = v___x_1801_;
goto v___jp_1798_;
}
v___jp_1781_:
{
if (v___y_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v___y_1782_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_1786_ = l_Lean_MessageData_ofConstName(v_declName_1772_, v___y_1784_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_Exception_toMessageData(v___y_1783_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1791_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1792_;
}
else
{
lean_dec_ref(v___y_1783_);
lean_dec(v_declName_1772_);
return v___y_1782_;
}
}
v___jp_1793_:
{
uint8_t v___x_1796_; 
v___x_1796_ = l_Lean_Exception_isInterrupt(v_a_1795_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
lean_inc_ref(v_a_1795_);
v___x_1797_ = l_Lean_Exception_isRuntime(v_a_1795_);
v___y_1782_ = v___y_1794_;
v___y_1783_ = v_a_1795_;
v___y_1784_ = v___x_1797_;
goto v___jp_1781_;
}
else
{
v___y_1782_ = v___y_1794_;
v___y_1783_ = v_a_1795_;
v___y_1784_ = v___x_1796_;
goto v___jp_1781_;
}
}
v___jp_1798_:
{
if (lean_obj_tag(v___y_1799_) == 0)
{
lean_dec(v_declName_1772_);
return v___y_1799_;
}
else
{
lean_object* v_a_1800_; 
v_a_1800_ = lean_ctor_get(v___y_1799_, 0);
lean_inc(v_a_1800_);
v___y_1794_ = v___y_1799_;
v_a_1795_ = v_a_1800_;
goto v___jp_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_declName_1831_, lean_object* v_a_1832_, lean_object* v___x_1833_, lean_object* v_declNameNonRec_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_1831_, v_a_1832_, v___x_1833_, v_declNameNonRec_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
if (lean_obj_tag(v_a_1841_) == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = l_List_reverse___redArg(v_a_1842_);
return v___x_1843_;
}
else
{
lean_object* v_head_1844_; lean_object* v_tail_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
v_head_1844_ = lean_ctor_get(v_a_1841_, 0);
v_tail_1845_ = lean_ctor_get(v_a_1841_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1841_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1847_ = v_a_1841_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_tail_1845_);
lean_inc(v_head_1844_);
lean_dec(v_a_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_Lean_mkLevelParam(v_head_1844_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v_a_1842_);
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1842_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v_a_1841_ = v_tail_1845_;
v_a_1842_ = v___x_1851_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_levelParams_1855_, lean_object* v_declName_1856_, lean_object* v_declNameNonRec_1857_, lean_object* v_name_1858_, lean_object* v_xs_1859_, lean_object* v_body_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_us_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1866_ = lean_box(0);
lean_inc(v_levelParams_1855_);
v_us_1867_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1855_, v___x_1866_);
lean_inc(v_declName_1856_);
v___x_1868_ = l_Lean_mkConst(v_declName_1856_, v_us_1867_);
v___x_1869_ = l_Lean_mkAppN(v___x_1868_, v_xs_1859_);
v___x_1870_ = l_Lean_Meta_mkEq(v___x_1869_, v_body_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___f_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc_n(v_a_1871_, 2);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = lean_box(0);
v___f_1873_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1873_, 0, v_declName_1856_);
lean_closure_set(v___f_1873_, 1, v_a_1871_);
lean_closure_set(v___f_1873_, 2, v___x_1872_);
lean_closure_set(v___f_1873_, 3, v_declNameNonRec_1857_);
v___x_1874_ = 0;
v___x_1875_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_1873_, v___x_1874_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; uint8_t v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1877_ = 1;
v___x_1878_ = 1;
v___x_1879_ = l_Lean_Meta_mkForallFVars(v_xs_1859_, v_a_1871_, v___x_1874_, v___x_1877_, v___x_1877_, v___x_1878_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = l_Lean_Meta_letToHave(v_a_1880_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = l_Lean_Meta_mkLambdaFVars(v_xs_1859_, v_a_1876_, v___x_1874_, v___x_1877_, v___x_1874_, v___x_1877_, v___x_1878_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
lean_inc(v_name_1858_);
v___x_1885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1885_, 0, v_name_1858_);
lean_ctor_set(v___x_1885_, 1, v_levelParams_1855_);
lean_ctor_set(v___x_1885_, 2, v_a_1882_);
v___x_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1886_, 0, v_name_1858_);
lean_ctor_set(v___x_1886_, 1, v___x_1866_);
v___x_1887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v_a_1884_);
lean_ctor_set(v___x_1887_, 2, v___x_1886_);
v___x_1888_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_1887_, v___y_1864_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_addDecl(v_a_1889_, v___x_1874_, v___y_1863_, v___y_1864_);
return v___x_1890_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1882_);
lean_dec(v_name_1858_);
lean_dec(v_levelParams_1855_);
v_a_1891_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1883_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1883_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1876_);
lean_dec(v_name_1858_);
lean_dec(v_levelParams_1855_);
v_a_1899_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1881_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1881_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1876_);
lean_dec(v_name_1858_);
lean_dec(v_levelParams_1855_);
v_a_1907_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1879_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1879_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1871_);
lean_dec(v_name_1858_);
lean_dec(v_levelParams_1855_);
v_a_1915_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1875_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1875_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_name_1858_);
lean_dec(v_declNameNonRec_1857_);
lean_dec(v_declName_1856_);
lean_dec(v_levelParams_1855_);
v_a_1923_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1870_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1870_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_levelParams_1931_, lean_object* v_declName_1932_, lean_object* v_declNameNonRec_1933_, lean_object* v_name_1934_, lean_object* v_xs_1935_, lean_object* v_body_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_1931_, v_declName_1932_, v_declNameNonRec_1933_, v_name_1934_, v_xs_1935_, v_body_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec_ref(v_xs_1935_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1943_, lean_object* v_info_1944_, lean_object* v_name_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v_levelParams_1952_; lean_object* v_value_1953_; lean_object* v_declNameNonRec_1954_; lean_object* v_fileName_1955_; lean_object* v_fileMap_1956_; lean_object* v_options_1957_; lean_object* v_currRecDepth_1958_; lean_object* v_ref_1959_; lean_object* v_currNamespace_1960_; lean_object* v_openDecls_1961_; lean_object* v_initHeartbeats_1962_; lean_object* v_maxHeartbeats_1963_; lean_object* v_quotContext_1964_; lean_object* v_currMacroScope_1965_; lean_object* v_cancelTk_x3f_1966_; uint8_t v_suppressElabErrors_1967_; lean_object* v_inheritedTraceOptions_1968_; lean_object* v_env_1969_; lean_object* v___f_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v_fileName_1977_; lean_object* v_fileMap_1978_; lean_object* v_currRecDepth_1979_; lean_object* v_ref_1980_; lean_object* v_currNamespace_1981_; lean_object* v_openDecls_1982_; lean_object* v_initHeartbeats_1983_; lean_object* v_maxHeartbeats_1984_; lean_object* v_quotContext_1985_; lean_object* v_currMacroScope_1986_; lean_object* v_cancelTk_x3f_1987_; uint8_t v_suppressElabErrors_1988_; lean_object* v_inheritedTraceOptions_1989_; lean_object* v___y_1990_; uint8_t v___y_1996_; uint8_t v___x_2017_; 
v___x_1951_ = lean_st_ref_get(v_a_1949_);
v_levelParams_1952_ = lean_ctor_get(v_info_1944_, 1);
lean_inc(v_levelParams_1952_);
v_value_1953_ = lean_ctor_get(v_info_1944_, 3);
lean_inc_ref(v_value_1953_);
v_declNameNonRec_1954_ = lean_ctor_get(v_info_1944_, 5);
lean_inc(v_declNameNonRec_1954_);
lean_dec_ref(v_info_1944_);
v_fileName_1955_ = lean_ctor_get(v_a_1948_, 0);
v_fileMap_1956_ = lean_ctor_get(v_a_1948_, 1);
v_options_1957_ = lean_ctor_get(v_a_1948_, 2);
v_currRecDepth_1958_ = lean_ctor_get(v_a_1948_, 3);
v_ref_1959_ = lean_ctor_get(v_a_1948_, 5);
v_currNamespace_1960_ = lean_ctor_get(v_a_1948_, 6);
v_openDecls_1961_ = lean_ctor_get(v_a_1948_, 7);
v_initHeartbeats_1962_ = lean_ctor_get(v_a_1948_, 8);
v_maxHeartbeats_1963_ = lean_ctor_get(v_a_1948_, 9);
v_quotContext_1964_ = lean_ctor_get(v_a_1948_, 10);
v_currMacroScope_1965_ = lean_ctor_get(v_a_1948_, 11);
v_cancelTk_x3f_1966_ = lean_ctor_get(v_a_1948_, 12);
v_suppressElabErrors_1967_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1968_ = lean_ctor_get(v_a_1948_, 13);
v_env_1969_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_ref(v_env_1969_);
lean_dec(v___x_1951_);
v___f_1970_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 4);
lean_closure_set(v___f_1970_, 0, v_levelParams_1952_);
lean_closure_set(v___f_1970_, 1, v_declName_1943_);
lean_closure_set(v___f_1970_, 2, v_declNameNonRec_1954_);
lean_closure_set(v___f_1970_, 3, v_name_1945_);
v___x_1971_ = 0;
v___x_1972_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_1957_);
v___x_1973_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1957_, v___x_1972_, v___x_1971_);
v___x_1974_ = l_Lean_diagnostics;
v___x_1975_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1973_, v___x_1974_);
v___x_2017_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1969_);
lean_dec_ref(v_env_1969_);
if (v___x_1975_ == 0)
{
if (v___x_2017_ == 0)
{
v_fileName_1977_ = v_fileName_1955_;
v_fileMap_1978_ = v_fileMap_1956_;
v_currRecDepth_1979_ = v_currRecDepth_1958_;
v_ref_1980_ = v_ref_1959_;
v_currNamespace_1981_ = v_currNamespace_1960_;
v_openDecls_1982_ = v_openDecls_1961_;
v_initHeartbeats_1983_ = v_initHeartbeats_1962_;
v_maxHeartbeats_1984_ = v_maxHeartbeats_1963_;
v_quotContext_1985_ = v_quotContext_1964_;
v_currMacroScope_1986_ = v_currMacroScope_1965_;
v_cancelTk_x3f_1987_ = v_cancelTk_x3f_1966_;
v_suppressElabErrors_1988_ = v_suppressElabErrors_1967_;
v_inheritedTraceOptions_1989_ = v_inheritedTraceOptions_1968_;
v___y_1990_ = v_a_1949_;
goto v___jp_1976_;
}
else
{
v___y_1996_ = v___x_1975_;
goto v___jp_1995_;
}
}
else
{
v___y_1996_ = v___x_2017_;
goto v___jp_1995_;
}
v___jp_1976_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = l_Lean_maxRecDepth;
v___x_1992_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_1973_, v___x_1991_);
lean_inc_ref(v_inheritedTraceOptions_1989_);
lean_inc(v_cancelTk_x3f_1987_);
lean_inc(v_currMacroScope_1986_);
lean_inc(v_quotContext_1985_);
lean_inc(v_maxHeartbeats_1984_);
lean_inc(v_initHeartbeats_1983_);
lean_inc(v_openDecls_1982_);
lean_inc(v_currNamespace_1981_);
lean_inc(v_ref_1980_);
lean_inc(v_currRecDepth_1979_);
lean_inc_ref(v_fileMap_1978_);
lean_inc_ref(v_fileName_1977_);
v___x_1993_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1993_, 0, v_fileName_1977_);
lean_ctor_set(v___x_1993_, 1, v_fileMap_1978_);
lean_ctor_set(v___x_1993_, 2, v___x_1973_);
lean_ctor_set(v___x_1993_, 3, v_currRecDepth_1979_);
lean_ctor_set(v___x_1993_, 4, v___x_1992_);
lean_ctor_set(v___x_1993_, 5, v_ref_1980_);
lean_ctor_set(v___x_1993_, 6, v_currNamespace_1981_);
lean_ctor_set(v___x_1993_, 7, v_openDecls_1982_);
lean_ctor_set(v___x_1993_, 8, v_initHeartbeats_1983_);
lean_ctor_set(v___x_1993_, 9, v_maxHeartbeats_1984_);
lean_ctor_set(v___x_1993_, 10, v_quotContext_1985_);
lean_ctor_set(v___x_1993_, 11, v_currMacroScope_1986_);
lean_ctor_set(v___x_1993_, 12, v_cancelTk_x3f_1987_);
lean_ctor_set(v___x_1993_, 13, v_inheritedTraceOptions_1989_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*14, v___x_1975_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*14 + 1, v_suppressElabErrors_1988_);
v___x_1994_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_1953_, v___f_1970_, v___x_1971_, v_a_1946_, v_a_1947_, v___x_1993_, v___y_1990_);
lean_dec_ref_known(v___x_1993_, 14);
return v___x_1994_;
}
v___jp_1995_:
{
if (v___y_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v_env_1998_; lean_object* v_nextMacroScope_1999_; lean_object* v_ngen_2000_; lean_object* v_auxDeclNGen_2001_; lean_object* v_traceState_2002_; lean_object* v_messages_2003_; lean_object* v_infoState_2004_; lean_object* v_snapshotTasks_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v___x_1997_ = lean_st_ref_take(v_a_1949_);
v_env_1998_ = lean_ctor_get(v___x_1997_, 0);
v_nextMacroScope_1999_ = lean_ctor_get(v___x_1997_, 1);
v_ngen_2000_ = lean_ctor_get(v___x_1997_, 2);
v_auxDeclNGen_2001_ = lean_ctor_get(v___x_1997_, 3);
v_traceState_2002_ = lean_ctor_get(v___x_1997_, 4);
v_messages_2003_ = lean_ctor_get(v___x_1997_, 6);
v_infoState_2004_ = lean_ctor_get(v___x_1997_, 7);
v_snapshotTasks_2005_ = lean_ctor_get(v___x_1997_, 8);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v___x_1997_, 5);
lean_dec(v_unused_2016_);
v___x_2007_ = v___x_1997_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snapshotTasks_2005_);
lean_inc(v_infoState_2004_);
lean_inc(v_messages_2003_);
lean_inc(v_traceState_2002_);
lean_inc(v_auxDeclNGen_2001_);
lean_inc(v_ngen_2000_);
lean_inc(v_nextMacroScope_1999_);
lean_inc(v_env_1998_);
lean_dec(v___x_1997_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2009_ = l_Lean_Kernel_enableDiag(v_env_1998_, v___x_1975_);
v___x_2010_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 5, v___x_2010_);
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_nextMacroScope_1999_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_ngen_2000_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_auxDeclNGen_2001_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_traceState_2002_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_messages_2003_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_infoState_2004_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_snapshotTasks_2005_);
v___x_2012_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_st_ref_put(v_a_1949_, v___x_2012_);
v_fileName_1977_ = v_fileName_1955_;
v_fileMap_1978_ = v_fileMap_1956_;
v_currRecDepth_1979_ = v_currRecDepth_1958_;
v_ref_1980_ = v_ref_1959_;
v_currNamespace_1981_ = v_currNamespace_1960_;
v_openDecls_1982_ = v_openDecls_1961_;
v_initHeartbeats_1983_ = v_initHeartbeats_1962_;
v_maxHeartbeats_1984_ = v_maxHeartbeats_1963_;
v_quotContext_1985_ = v_quotContext_1964_;
v_currMacroScope_1986_ = v_currMacroScope_1965_;
v_cancelTk_x3f_1987_ = v_cancelTk_x3f_1966_;
v_suppressElabErrors_1988_ = v_suppressElabErrors_1967_;
v_inheritedTraceOptions_1989_ = v_inheritedTraceOptions_1968_;
v___y_1990_ = v_a_1949_;
goto v___jp_1976_;
}
}
}
else
{
v_fileName_1977_ = v_fileName_1955_;
v_fileMap_1978_ = v_fileMap_1956_;
v_currRecDepth_1979_ = v_currRecDepth_1958_;
v_ref_1980_ = v_ref_1959_;
v_currNamespace_1981_ = v_currNamespace_1960_;
v_openDecls_1982_ = v_openDecls_1961_;
v_initHeartbeats_1983_ = v_initHeartbeats_1962_;
v_maxHeartbeats_1984_ = v_maxHeartbeats_1963_;
v_quotContext_1985_ = v_quotContext_1964_;
v_currMacroScope_1986_ = v_currMacroScope_1965_;
v_cancelTk_x3f_1987_ = v_cancelTk_x3f_1966_;
v_suppressElabErrors_1988_ = v_suppressElabErrors_1967_;
v_inheritedTraceOptions_1989_ = v_inheritedTraceOptions_1968_;
v___y_1990_ = v_a_1949_;
goto v___jp_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2018_, lean_object* v_info_2019_, lean_object* v_name_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2018_, v_info_2019_, v_name_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2027_, lean_object* v_info_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v_env_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2034_ = lean_st_ref_get(v_a_2032_);
v_env_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_env_2035_);
lean_dec(v___x_2034_);
v___x_2036_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_2027_, 2);
v___x_2037_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2035_, v_declName_2027_, v___x_2036_);
lean_inc_n(v___x_2037_, 2);
v___x_2038_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2038_, 0, v_declName_2027_);
lean_closure_set(v___x_2038_, 1, v_info_2028_);
lean_closure_set(v___x_2038_, 2, v___x_2037_);
v___x_2039_ = l_Lean_Meta_realizeConst(v_declName_2027_, v___x_2037_, v___x_2038_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2047_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2037_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2037_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v___x_2037_);
v_a_2048_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2039_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2039_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2056_, lean_object* v_info_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2056_, v_info_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_env_2072_; lean_object* v_env_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; 
v___x_2070_ = lean_st_ref_get(v_a_2068_);
v___x_2071_ = lean_st_ref_get(v_a_2068_);
v_env_2072_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_ref(v_env_2072_);
lean_dec(v___x_2070_);
v_env_2073_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_ref_n(v_env_2073_, 2);
lean_dec(v___x_2071_);
v___x_2074_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2064_);
v___x_2075_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2072_, v_declName_2064_, v___x_2074_);
v___x_2076_ = 1;
lean_inc(v___x_2075_);
v___x_2077_ = l_Lean_Environment_contains(v_env_2073_, v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v_toEnvExtension_2079_; lean_object* v_asyncMode_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v___x_2075_);
v___x_2078_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2079_ = lean_ctor_get(v___x_2078_, 0);
v_asyncMode_2080_ = lean_ctor_get(v_toEnvExtension_2079_, 2);
v___x_2081_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2082_ = 0;
lean_inc(v_declName_2064_);
v___x_2083_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2081_, v___x_2078_, v_env_2073_, v_declName_2064_, v_asyncMode_2080_, v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2108_; 
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2108_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_val_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2108_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2064_, v_val_2084_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_a_2089_);
v___x_2094_ = v___x_2086_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2094_);
v___x_2096_ = v___x_2091_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_del_object(v___x_2086_);
v_a_2100_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2088_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2088_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___x_2083_);
lean_dec(v_declName_2064_);
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref(v_env_2073_);
lean_dec(v_declName_2064_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2075_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2123_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2125_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
