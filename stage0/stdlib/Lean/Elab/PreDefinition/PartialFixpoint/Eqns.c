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
uint8_t v___x_4040__boxed_94_; uint8_t v___x_4041__boxed_95_; uint8_t v_____do__lift_4042__boxed_96_; lean_object* v_res_97_; 
v___x_4040__boxed_94_ = lean_unbox(v___x_86_);
v___x_4041__boxed_95_ = lean_unbox(v___x_87_);
v_____do__lift_4042__boxed_96_ = lean_unbox(v_____do__lift_88_);
v_res_97_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4040__boxed_94_, v___x_4041__boxed_95_, v_____do__lift_4042__boxed_96_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
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
lean_object* v___x_102_; uint8_t v_kind_103_; uint8_t v___x_104_; uint8_t v___x_105_; 
v___x_102_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
v_kind_103_ = lean_ctor_get_uint8(v___x_102_, sizeof(void*)*9);
v___x_104_ = 1;
v___x_105_ = l_Lean_Elab_DefKind_isTheorem(v_kind_103_);
if (v___x_105_ == 0)
{
return v___x_104_;
}
else
{
if (v___x_101_ == 0)
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_99_, v___x_106_);
v_i_99_ = v___x_107_;
goto _start;
}
else
{
return v___x_104_;
}
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
uint8_t v___x_4145__boxed_230_; size_t v_i_boxed_231_; size_t v_stop_boxed_232_; lean_object* v_res_233_; 
v___x_4145__boxed_230_ = lean_unbox(v___x_221_);
v_i_boxed_231_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_stop_boxed_232_ = lean_unbox_usize(v_stop_224_);
lean_dec(v_stop_224_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4145__boxed_230_, v_as_222_, v_i_boxed_231_, v_stop_boxed_232_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
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
v___x_264_ = lean_st_ref_set(v_a_248_, v___x_263_);
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
v___x_276_ = lean_st_ref_set(v_a_246_, v___x_275_);
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
v___x_323_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_321_, v___x_322_, v___x_322_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
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
v___x_598_ = lean_unsigned_to_nat(1898u);
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
lean_object* v___f_724_; lean_object* v___x_1534__overap_725_; lean_object* v___x_726_; 
v___f_724_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1534__overap_725_ = lean_panic_fn_borrowed(v___f_724_, v_msg_718_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
v___x_726_ = lean_apply_5(v___x_1534__overap_725_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
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
lean_object* v_ks_821_; lean_object* v_vs_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_842_; 
v_ks_821_ = lean_ctor_get(v_x_770_, 0);
v_vs_822_ = lean_ctor_get(v_x_770_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_842_ == 0)
{
v___x_824_ = v_x_770_;
v_isShared_825_ = v_isSharedCheck_842_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_vs_822_);
lean_inc(v_ks_821_);
lean_dec(v_x_770_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_842_;
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
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_ks_821_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_vs_822_);
v___x_827_ = v_reuseFailAlloc_841_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v_newNode_828_; uint8_t v___y_830_; size_t v___x_836_; uint8_t v___x_837_; 
v_newNode_828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_827_, v_x_773_, v_x_774_);
v___x_836_ = ((size_t)7ULL);
v___x_837_ = lean_usize_dec_le(v___x_836_, v_x_772_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_828_);
v___x_839_ = lean_unsigned_to_nat(4u);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
v___y_830_ = v___x_840_;
goto v___jp_829_;
}
else
{
v___y_830_ = v___x_837_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_object* v_ks_831_; lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_ks_831_ = lean_ctor_get(v_newNode_828_, 0);
lean_inc_ref(v_ks_831_);
v_vs_832_ = lean_ctor_get(v_newNode_828_, 1);
lean_inc_ref(v_vs_832_);
lean_dec_ref(v_newNode_828_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_772_, v_ks_831_, v_vs_832_, v___x_833_, v___x_834_);
lean_dec_ref(v_vs_832_);
lean_dec_ref(v_ks_831_);
return v___x_835_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_843_, lean_object* v_keys_844_, lean_object* v_vals_845_, lean_object* v_i_846_, lean_object* v_entries_847_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_array_get_size(v_keys_844_);
v___x_849_ = lean_nat_dec_lt(v_i_846_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec(v_i_846_);
return v_entries_847_;
}
else
{
lean_object* v_k_850_; lean_object* v_v_851_; uint64_t v___x_852_; size_t v_h_853_; size_t v___x_854_; lean_object* v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v_h_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_k_850_ = lean_array_fget_borrowed(v_keys_844_, v_i_846_);
v_v_851_ = lean_array_fget_borrowed(v_vals_845_, v_i_846_);
v___x_852_ = l_Lean_instHashableMVarId_hash(v_k_850_);
v_h_853_ = lean_uint64_to_usize(v___x_852_);
v___x_854_ = ((size_t)5ULL);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_sub(v_depth_843_, v___x_856_);
v___x_858_ = lean_usize_mul(v___x_854_, v___x_857_);
v_h_859_ = lean_usize_shift_right(v_h_853_, v___x_858_);
v___x_860_ = lean_nat_add(v_i_846_, v___x_855_);
lean_dec(v_i_846_);
lean_inc(v_v_851_);
lean_inc(v_k_850_);
v___x_861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_847_, v_h_859_, v_depth_843_, v_k_850_, v_v_851_);
v_i_846_ = v___x_860_;
v_entries_847_ = v___x_861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_863_, lean_object* v_keys_864_, lean_object* v_vals_865_, lean_object* v_i_866_, lean_object* v_entries_867_){
_start:
{
size_t v_depth_boxed_868_; lean_object* v_res_869_; 
v_depth_boxed_868_ = lean_unbox_usize(v_depth_863_);
lean_dec(v_depth_863_);
v_res_869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_868_, v_keys_864_, v_vals_865_, v_i_866_, v_entries_867_);
lean_dec_ref(v_vals_865_);
lean_dec_ref(v_keys_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
size_t v_x_2109__boxed_875_; size_t v_x_2110__boxed_876_; lean_object* v_res_877_; 
v_x_2109__boxed_875_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_x_2110__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_res_877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_870_, v_x_2109__boxed_875_, v_x_2110__boxed_876_, v_x_873_, v_x_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
uint64_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_881_ = l_Lean_instHashableMVarId_hash(v_x_879_);
v___x_882_ = lean_uint64_to_usize(v___x_881_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_878_, v___x_882_, v___x_883_, v_x_879_, v_x_880_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_885_, lean_object* v_val_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v_mctx_890_; lean_object* v_cache_891_; lean_object* v_zetaDeltaFVarIds_892_; lean_object* v_postponed_893_; lean_object* v_diag_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_922_; 
v___x_889_ = lean_st_ref_take(v___y_887_);
v_mctx_890_ = lean_ctor_get(v___x_889_, 0);
v_cache_891_ = lean_ctor_get(v___x_889_, 1);
v_zetaDeltaFVarIds_892_ = lean_ctor_get(v___x_889_, 2);
v_postponed_893_ = lean_ctor_get(v___x_889_, 3);
v_diag_894_ = lean_ctor_get(v___x_889_, 4);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_922_ == 0)
{
v___x_896_ = v___x_889_;
v_isShared_897_ = v_isSharedCheck_922_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_diag_894_);
lean_inc(v_postponed_893_);
lean_inc(v_zetaDeltaFVarIds_892_);
lean_inc(v_cache_891_);
lean_inc(v_mctx_890_);
lean_dec(v___x_889_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_922_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_depth_898_; lean_object* v_levelAssignDepth_899_; lean_object* v_lmvarCounter_900_; lean_object* v_mvarCounter_901_; lean_object* v_lDecls_902_; lean_object* v_decls_903_; lean_object* v_userNames_904_; lean_object* v_lAssignment_905_; lean_object* v_eAssignment_906_; lean_object* v_dAssignment_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_921_; 
v_depth_898_ = lean_ctor_get(v_mctx_890_, 0);
v_levelAssignDepth_899_ = lean_ctor_get(v_mctx_890_, 1);
v_lmvarCounter_900_ = lean_ctor_get(v_mctx_890_, 2);
v_mvarCounter_901_ = lean_ctor_get(v_mctx_890_, 3);
v_lDecls_902_ = lean_ctor_get(v_mctx_890_, 4);
v_decls_903_ = lean_ctor_get(v_mctx_890_, 5);
v_userNames_904_ = lean_ctor_get(v_mctx_890_, 6);
v_lAssignment_905_ = lean_ctor_get(v_mctx_890_, 7);
v_eAssignment_906_ = lean_ctor_get(v_mctx_890_, 8);
v_dAssignment_907_ = lean_ctor_get(v_mctx_890_, 9);
v_isSharedCheck_921_ = !lean_is_exclusive(v_mctx_890_);
if (v_isSharedCheck_921_ == 0)
{
v___x_909_ = v_mctx_890_;
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_dAssignment_907_);
lean_inc(v_eAssignment_906_);
lean_inc(v_lAssignment_905_);
lean_inc(v_userNames_904_);
lean_inc(v_decls_903_);
lean_inc(v_lDecls_902_);
lean_inc(v_mvarCounter_901_);
lean_inc(v_lmvarCounter_900_);
lean_inc(v_levelAssignDepth_899_);
lean_inc(v_depth_898_);
lean_dec(v_mctx_890_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_906_, v_mvarId_885_, v_val_886_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 8, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_depth_898_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_levelAssignDepth_899_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_lmvarCounter_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_mvarCounter_901_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_lDecls_902_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_decls_903_);
lean_ctor_set(v_reuseFailAlloc_920_, 6, v_userNames_904_);
lean_ctor_set(v_reuseFailAlloc_920_, 7, v_lAssignment_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 8, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 9, v_dAssignment_907_);
v___x_913_ = v_reuseFailAlloc_920_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_913_);
v___x_915_ = v___x_896_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_cache_891_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_zetaDeltaFVarIds_892_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_postponed_893_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_diag_894_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_set(v___y_887_, v___x_915_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_923_, lean_object* v_val_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_923_, v_val_924_, v___y_925_);
lean_dec(v___y_925_);
return v_res_927_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_932_ = lean_unsigned_to_nat(41u);
v___x_933_ = lean_unsigned_to_nat(70u);
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_936_ = l_mkPanicMessageWithDecl(v___x_935_, v___x_934_, v___x_933_, v___x_932_, v___x_931_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_938_ = lean_unsigned_to_nat(51u);
v___x_939_ = lean_unsigned_to_nat(72u);
v___x_940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_942_ = l_mkPanicMessageWithDecl(v___x_941_, v___x_940_, v___x_939_, v___x_938_, v___x_937_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
lean_inc(v_mvarId_943_);
v___x_949_ = l_Lean_MVarId_getType_x27(v_mvarId_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_952_ = lean_unsigned_to_nat(3u);
v___x_953_ = l_Lean_Expr_isAppOfArity(v_a_950_, v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_a_950_);
lean_dec(v_mvarId_943_);
v___x_954_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_955_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_954_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = l_Lean_Expr_appFn_x21(v_a_950_);
v___x_957_ = l_Lean_Expr_appArg_x21(v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_957_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_n(v_a_959_, 2);
lean_dec_ref_known(v___x_958_, 1);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
v___x_960_ = lean_infer_type(v_a_959_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_Lean_Expr_isAppOfArity(v_a_961_, v___x_951_, v___x_952_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_950_);
lean_dec(v_mvarId_943_);
v___x_963_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_964_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_963_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_Expr_appArg_x21(v_a_950_);
lean_dec(v_a_950_);
v___x_966_ = l_Lean_Expr_appArg_x21(v_a_961_);
lean_dec(v_a_961_);
v___x_967_ = l_Lean_Meta_mkEq(v___x_966_, v___x_965_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = lean_box(0);
v___x_970_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_968_, v___x_969_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_n(v_a_971_, 2);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = l_Lean_Meta_mkEqTrans(v_a_959_, v_a_971_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v___y_944_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_943_, v_a_973_, v___y_945_);
lean_dec(v___y_945_);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_983_);
v___x_976_ = v___x_974_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_974_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_Expr_mvarId_x21(v_a_971_);
lean_dec(v_a_971_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_971_);
lean_dec(v___y_945_);
lean_dec(v_mvarId_943_);
v_a_984_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_972_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_972_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_a_959_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_mvarId_943_);
v_a_992_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_970_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_970_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_a_959_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_mvarId_943_);
v_a_1000_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_967_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_967_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_959_);
lean_dec(v_a_950_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_mvarId_943_);
v_a_1008_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_960_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_960_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_950_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_mvarId_943_);
v_a_1016_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_958_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_958_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_mvarId_943_);
v_a_1024_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_949_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_949_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___f_1045_; lean_object* v___x_1046_; 
lean_inc(v_mvarId_1039_);
v___f_1045_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1045_, 0, v_mvarId_1039_);
v___x_1046_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1039_, v___f_1045_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1054_, lean_object* v_val_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1054_, v_val_1055_, v___y_1057_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1062_, lean_object* v_val_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1062_, v_val_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1071_, v_x_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, size_t v_x_1077_, size_t v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1076_, v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
size_t v_x_2589__boxed_1088_; size_t v_x_2590__boxed_1089_; lean_object* v_res_1090_; 
v_x_2589__boxed_1088_ = lean_unbox_usize(v_x_1084_);
lean_dec(v_x_1084_);
v_x_2590__boxed_1089_ = lean_unbox_usize(v_x_1085_);
lean_dec(v_x_1085_);
v_res_1090_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1082_, v_x_1083_, v_x_2589__boxed_1088_, v_x_2590__boxed_1089_, v_x_1086_, v_x_1087_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1091_, lean_object* v_n_1092_, lean_object* v_k_1093_, lean_object* v_v_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1092_, v_k_1093_, v_v_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1096_, size_t v_depth_1097_, lean_object* v_keys_1098_, lean_object* v_vals_1099_, lean_object* v_heq_1100_, lean_object* v_i_1101_, lean_object* v_entries_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1097_, v_keys_1098_, v_vals_1099_, v_i_1101_, v_entries_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1104_, lean_object* v_depth_1105_, lean_object* v_keys_1106_, lean_object* v_vals_1107_, lean_object* v_heq_1108_, lean_object* v_i_1109_, lean_object* v_entries_1110_){
_start:
{
size_t v_depth_boxed_1111_; lean_object* v_res_1112_; 
v_depth_boxed_1111_ = lean_unbox_usize(v_depth_1105_);
lean_dec(v_depth_1105_);
v_res_1112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1104_, v_depth_boxed_1111_, v_keys_1106_, v_vals_1107_, v_heq_1108_, v_i_1109_, v_entries_1110_);
lean_dec_ref(v_vals_1107_);
lean_dec_ref(v_keys_1106_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1119_, lean_object* v_opt_1120_){
_start:
{
lean_object* v_name_1121_; lean_object* v_defValue_1122_; lean_object* v_map_1123_; lean_object* v___x_1124_; 
v_name_1121_ = lean_ctor_get(v_opt_1120_, 0);
v_defValue_1122_ = lean_ctor_get(v_opt_1120_, 1);
v_map_1123_ = lean_ctor_get(v_opts_1119_, 0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1123_, v_name_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_unbox(v_defValue_1122_);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; 
v_val_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1124_, 1);
if (lean_obj_tag(v_val_1126_) == 1)
{
uint8_t v_v_1127_; 
v_v_1127_ = lean_ctor_get_uint8(v_val_1126_, 0);
lean_dec_ref_known(v_val_1126_, 0);
return v_v_1127_;
}
else
{
uint8_t v___x_1128_; 
lean_dec(v_val_1126_);
v___x_1128_ = lean_unbox(v_defValue_1122_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1129_, lean_object* v_opt_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1129_, v_opt_1130_);
lean_dec_ref(v_opt_1130_);
lean_dec_ref(v_opts_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1133_, lean_object* v_opt_1134_){
_start:
{
lean_object* v_name_1135_; lean_object* v_defValue_1136_; lean_object* v_map_1137_; lean_object* v___x_1138_; 
v_name_1135_ = lean_ctor_get(v_opt_1134_, 0);
v_defValue_1136_ = lean_ctor_get(v_opt_1134_, 1);
v_map_1137_ = lean_ctor_get(v_opts_1133_, 0);
v___x_1138_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1137_, v_name_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_inc(v_defValue_1136_);
return v_defValue_1136_;
}
else
{
lean_object* v_val_1139_; 
v_val_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v___x_1138_, 1);
if (lean_obj_tag(v_val_1139_) == 3)
{
lean_object* v_v_1140_; 
v_v_1140_ = lean_ctor_get(v_val_1139_, 0);
lean_inc(v_v_1140_);
lean_dec_ref_known(v_val_1139_, 1);
return v_v_1140_;
}
else
{
lean_dec(v_val_1139_);
lean_inc(v_defValue_1136_);
return v_defValue_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1141_, lean_object* v_opt_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1141_, v_opt_1142_);
lean_dec_ref(v_opt_1142_);
lean_dec_ref(v_opts_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_e_1144_, lean_object* v___y_1145_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = l_Lean_Expr_hasMVar(v_e_1144_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_e_1144_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v_mctx_1150_; lean_object* v___x_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1154_; lean_object* v_cache_1155_; lean_object* v_zetaDeltaFVarIds_1156_; lean_object* v_postponed_1157_; lean_object* v_diag_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1167_; 
v___x_1149_ = lean_st_ref_get(v___y_1145_);
v_mctx_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_mctx_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_instantiateMVarsCore(v_mctx_1150_, v_e_1144_);
v_fst_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_fst_1152_);
v_snd_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1153_);
lean_dec_ref(v___x_1151_);
v___x_1154_ = lean_st_ref_take(v___y_1145_);
v_cache_1155_ = lean_ctor_get(v___x_1154_, 1);
v_zetaDeltaFVarIds_1156_ = lean_ctor_get(v___x_1154_, 2);
v_postponed_1157_ = lean_ctor_get(v___x_1154_, 3);
v_diag_1158_ = lean_ctor_get(v___x_1154_, 4);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v___x_1154_, 0);
lean_dec(v_unused_1168_);
v___x_1160_ = v___x_1154_;
v_isShared_1161_ = v_isSharedCheck_1167_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_diag_1158_);
lean_inc(v_postponed_1157_);
lean_inc(v_zetaDeltaFVarIds_1156_);
lean_inc(v_cache_1155_);
lean_dec(v___x_1154_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1167_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_snd_1153_);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_snd_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_cache_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_zetaDeltaFVarIds_1156_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_postponed_1157_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_diag_1158_);
v___x_1163_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_st_ref_set(v___y_1145_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_fst_1152_);
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_e_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1169_, v___y_1170_);
lean_dec(v___y_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_e_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1173_, v___y_1175_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_e_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_e_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(lean_object* v_k_1187_, uint8_t v_allowLevelAssignments_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1188_, v_k_1187_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg___boxed(lean_object* v_k_1211_, lean_object* v_allowLevelAssignments_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1218_; lean_object* v_res_1219_; 
v_allowLevelAssignments_boxed_1218_ = lean_unbox(v_allowLevelAssignments_1212_);
v_res_1219_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1211_, v_allowLevelAssignments_boxed_1218_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object* v_00_u03b1_1220_, lean_object* v_k_1221_, uint8_t v_allowLevelAssignments_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1221_, v_allowLevelAssignments_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_k_1230_, lean_object* v_allowLevelAssignments_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1237_; lean_object* v_res_1238_; 
v_allowLevelAssignments_boxed_1237_ = lean_unbox(v_allowLevelAssignments_1231_);
v_res_1238_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_00_u03b1_1229_, v_k_1230_, v_allowLevelAssignments_boxed_1237_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object* v_thm_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_env_1243_; lean_object* v_toConstantVal_1244_; lean_object* v_value_1245_; lean_object* v_all_1246_; uint8_t v___y_1248_; lean_object* v_type_1256_; uint8_t v___x_1257_; 
v___x_1242_ = lean_st_ref_get(v___y_1240_);
v_env_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref_n(v_env_1243_, 2);
lean_dec(v___x_1242_);
v_toConstantVal_1244_ = lean_ctor_get(v_thm_1239_, 0);
v_value_1245_ = lean_ctor_get(v_thm_1239_, 1);
v_all_1246_ = lean_ctor_get(v_thm_1239_, 2);
v_type_1256_ = lean_ctor_get(v_toConstantVal_1244_, 2);
v___x_1257_ = l_Lean_Environment_hasUnsafe(v_env_1243_, v_type_1256_);
if (v___x_1257_ == 0)
{
uint8_t v___x_1258_; 
v___x_1258_ = l_Lean_Environment_hasUnsafe(v_env_1243_, v_value_1245_);
v___y_1248_ = v___x_1258_;
goto v___jp_1247_;
}
else
{
lean_dec_ref(v_env_1243_);
v___y_1248_ = v___x_1257_;
goto v___jp_1247_;
}
v___jp_1247_:
{
if (v___y_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_thm_1239_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_inc(v_all_1246_);
lean_inc_ref(v_value_1245_);
lean_inc_ref(v_toConstantVal_1244_);
lean_dec_ref(v_thm_1239_);
v___x_1251_ = lean_box(0);
v___x_1252_ = 0;
v___x_1253_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1253_, 0, v_toConstantVal_1244_);
lean_ctor_set(v___x_1253_, 1, v_value_1245_);
lean_ctor_set(v___x_1253_, 2, v___x_1251_);
lean_ctor_set(v___x_1253_, 3, v_all_1246_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*4, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object* v_thm_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1259_, v___y_1260_);
lean_dec(v___y_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object* v_thm_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1263_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object* v_thm_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_thm_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(lean_object* v_k_1277_, lean_object* v_b_1278_, lean_object* v_c_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1285_ = lean_apply_7(v_k_1277_, v_b_1278_, v_c_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, lean_box(0));
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(lean_object* v_k_1286_, lean_object* v_b_1287_, lean_object* v_c_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(v_k_1286_, v_b_1287_, v_c_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object* v_e_1295_, lean_object* v_k_1296_, uint8_t v_cleanupAnnotations_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___f_1303_; uint8_t v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1303_, 0, v_k_1296_);
v___x_1304_ = 1;
v___x_1305_ = 0;
v___x_1306_ = lean_box(0);
v___x_1307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1295_, v___x_1304_, v___x_1305_, v___x_1304_, v___x_1305_, v___x_1306_, v___f_1303_, v_cleanupAnnotations_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1307_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1307_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object* v_e_1324_, lean_object* v_k_1325_, lean_object* v_cleanupAnnotations_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1332_; lean_object* v_res_1333_; 
v_cleanupAnnotations_boxed_1332_ = lean_unbox(v_cleanupAnnotations_1326_);
v_res_1333_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1324_, v_k_1325_, v_cleanupAnnotations_boxed_1332_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object* v_00_u03b1_1334_, lean_object* v_e_1335_, lean_object* v_k_1336_, uint8_t v_cleanupAnnotations_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1335_, v_k_1336_, v_cleanupAnnotations_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_e_1345_, lean_object* v_k_1346_, lean_object* v_cleanupAnnotations_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1353_; lean_object* v_res_1354_; 
v_cleanupAnnotations_boxed_1353_ = lean_unbox(v_cleanupAnnotations_1347_);
v_res_1354_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_00_u03b1_1344_, v_e_1345_, v_k_1346_, v_cleanupAnnotations_boxed_1353_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_options_1364_; uint8_t v_hasTrace_1365_; 
v_options_1364_ = lean_ctor_get(v___y_1361_, 2);
v_hasTrace_1365_ = lean_ctor_get_uint8(v_options_1364_, sizeof(void*)*1);
if (v_hasTrace_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v___x_1358_);
v___x_1366_ = lean_box(v_hasTrace_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_inheritedTraceOptions_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_inheritedTraceOptions_1368_ = lean_ctor_get(v___y_1361_, 13);
v___x_1369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1370_ = l_Lean_Name_append(v___x_1369_, v___x_1358_);
v___x_1371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1368_, v_options_1364_, v___x_1370_);
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1380_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1381_; double v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_float_of_nat(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object* v_cls_1386_, lean_object* v_msg_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_ref_1393_; lean_object* v___x_1394_; lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1439_; 
v_ref_1393_ = lean_ctor_get(v___y_1390_, 5);
v___x_1394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1439_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1439_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v_traceState_1400_; lean_object* v_env_1401_; lean_object* v_nextMacroScope_1402_; lean_object* v_ngen_1403_; lean_object* v_auxDeclNGen_1404_; lean_object* v_cache_1405_; lean_object* v_messages_1406_; lean_object* v_infoState_1407_; lean_object* v_snapshotTasks_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1438_; 
v___x_1399_ = lean_st_ref_take(v___y_1391_);
v_traceState_1400_ = lean_ctor_get(v___x_1399_, 4);
v_env_1401_ = lean_ctor_get(v___x_1399_, 0);
v_nextMacroScope_1402_ = lean_ctor_get(v___x_1399_, 1);
v_ngen_1403_ = lean_ctor_get(v___x_1399_, 2);
v_auxDeclNGen_1404_ = lean_ctor_get(v___x_1399_, 3);
v_cache_1405_ = lean_ctor_get(v___x_1399_, 5);
v_messages_1406_ = lean_ctor_get(v___x_1399_, 6);
v_infoState_1407_ = lean_ctor_get(v___x_1399_, 7);
v_snapshotTasks_1408_ = lean_ctor_get(v___x_1399_, 8);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1410_ = v___x_1399_;
v_isShared_1411_ = v_isSharedCheck_1438_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snapshotTasks_1408_);
lean_inc(v_infoState_1407_);
lean_inc(v_messages_1406_);
lean_inc(v_cache_1405_);
lean_inc(v_traceState_1400_);
lean_inc(v_auxDeclNGen_1404_);
lean_inc(v_ngen_1403_);
lean_inc(v_nextMacroScope_1402_);
lean_inc(v_env_1401_);
lean_dec(v___x_1399_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1438_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint64_t v_tid_1412_; lean_object* v_traces_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1437_; 
v_tid_1412_ = lean_ctor_get_uint64(v_traceState_1400_, sizeof(void*)*1);
v_traces_1413_ = lean_ctor_get(v_traceState_1400_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_traceState_1400_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1415_ = v_traceState_1400_;
v_isShared_1416_ = v_isSharedCheck_1437_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_traces_1413_);
lean_dec(v_traceState_1400_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1437_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; double v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0);
v___x_1419_ = 0;
v___x_1420_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1));
v___x_1421_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1421_, 0, v_cls_1386_);
lean_ctor_set(v___x_1421_, 1, v___x_1417_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
lean_ctor_set_float(v___x_1421_, sizeof(void*)*3, v___x_1418_);
lean_ctor_set_float(v___x_1421_, sizeof(void*)*3 + 8, v___x_1418_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*3 + 16, v___x_1419_);
v___x_1422_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2));
v___x_1423_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v_a_1395_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
lean_inc(v_ref_1393_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_ref_1393_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Lean_PersistentArray_push___redArg(v_traces_1413_, v___x_1424_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1425_);
v___x_1427_ = v___x_1415_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1425_);
lean_ctor_set_uint64(v_reuseFailAlloc_1436_, sizeof(void*)*1, v_tid_1412_);
v___x_1427_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v___x_1427_);
v___x_1429_ = v___x_1410_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_env_1401_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_nextMacroScope_1402_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_ngen_1403_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_auxDeclNGen_1404_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1435_, 5, v_cache_1405_);
lean_ctor_set(v_reuseFailAlloc_1435_, 6, v_messages_1406_);
lean_ctor_set(v_reuseFailAlloc_1435_, 7, v_infoState_1407_);
lean_ctor_set(v_reuseFailAlloc_1435_, 8, v_snapshotTasks_1408_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_st_ref_set(v___y_1391_, v___x_1429_);
v___x_1431_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1431_);
v___x_1433_ = v___x_1397_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object* v_cls_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_cls_1440_, v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_o_1448_, lean_object* v_k_1449_, uint8_t v_v_1450_){
_start:
{
lean_object* v_map_1451_; uint8_t v_hasTrace_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1466_; 
v_map_1451_ = lean_ctor_get(v_o_1448_, 0);
v_hasTrace_1452_ = lean_ctor_get_uint8(v_o_1448_, sizeof(void*)*1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_o_1448_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1454_ = v_o_1448_;
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_map_1451_);
lean_dec(v_o_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1456_, 0, v_v_1450_);
lean_inc(v_k_1449_);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1449_, v___x_1456_, v_map_1451_);
if (v_hasTrace_1452_ == 0)
{
lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1459_ = l_Lean_Name_isPrefixOf(v___x_1458_, v_k_1449_);
lean_dec(v_k_1449_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1457_);
v___x_1461_ = v___x_1454_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1457_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*1, v___x_1459_);
return v___x_1461_;
}
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_k_1449_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1457_);
v___x_1464_ = v___x_1454_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*1, v_hasTrace_1452_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_o_1467_, lean_object* v_k_1468_, lean_object* v_v_1469_){
_start:
{
uint8_t v_v_boxed_1470_; lean_object* v_res_1471_; 
v_v_boxed_1470_ = lean_unbox(v_v_1469_);
v_res_1471_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_o_1467_, v_k_1468_, v_v_boxed_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_opts_1472_, lean_object* v_opt_1473_, uint8_t v_val_1474_){
_start:
{
lean_object* v_name_1475_; lean_object* v___x_1476_; 
v_name_1475_ = lean_ctor_get(v_opt_1473_, 0);
lean_inc(v_name_1475_);
lean_dec_ref(v_opt_1473_);
v___x_1476_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_opts_1472_, v_name_1475_, v_val_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_opts_1477_, lean_object* v_opt_1478_, lean_object* v_val_1479_){
_start:
{
uint8_t v_val_boxed_1480_; lean_object* v_res_1481_; 
v_val_boxed_1480_ = lean_unbox(v_val_1479_);
v_res_1481_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_opts_1477_, v_opt_1478_, v_val_boxed_1480_);
return v_res_1481_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0));
v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_declName_1491_, lean_object* v_declNameNonRec_1492_, lean_object* v___x_1493_, lean_object* v___f_1494_, lean_object* v_a_1495_, lean_object* v___x_1496_, lean_object* v_____r_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___y_1504_; lean_object* v___y_1505_; uint8_t v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; uint8_t v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v_fileName_1515_; lean_object* v_fileMap_1516_; lean_object* v_currRecDepth_1517_; lean_object* v_ref_1518_; lean_object* v_currNamespace_1519_; lean_object* v_openDecls_1520_; lean_object* v_initHeartbeats_1521_; lean_object* v_maxHeartbeats_1522_; lean_object* v_quotContext_1523_; lean_object* v_currMacroScope_1524_; lean_object* v_cancelTk_x3f_1525_; uint8_t v_suppressElabErrors_1526_; lean_object* v_inheritedTraceOptions_1527_; lean_object* v___y_1528_; lean_object* v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; uint8_t v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; uint8_t v___y_1597_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; uint8_t v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; uint8_t v___y_1625_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___x_1703_; 
v___x_1703_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1491_, v_declNameNonRec_1492_, v___x_1493_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___x_1743_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
lean_inc_ref(v___f_1494_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
v___x_1743_ = lean_apply_5(v___f_1494_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; uint8_t v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = lean_unbox(v_a_1744_);
lean_dec(v_a_1744_);
if (v___x_1745_ == 0)
{
v___y_1706_ = v___y_1498_;
v___y_1707_ = v___y_1499_;
v___y_1708_ = v___y_1500_;
v___y_1709_ = v___y_1501_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
lean_inc(v_a_1704_);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1704_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
lean_inc(v___x_1496_);
v___x_1749_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1496_, v___x_1748_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_dec_ref_known(v___x_1749_, 1);
v___y_1706_ = v___y_1498_;
v___y_1707_ = v___y_1499_;
v___y_1708_ = v___y_1500_;
v___y_1709_ = v___y_1501_;
goto v___jp_1705_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_a_1704_);
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
lean_dec_ref(v___f_1494_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1704_);
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
lean_dec_ref(v___f_1494_);
v_a_1758_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1743_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1743_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
v___jp_1705_:
{
lean_object* v___x_1710_; 
v___x_1710_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1704_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
v___x_1712_ = lean_apply_5(v___f_1494_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, lean_box(0));
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
if (v___x_1714_ == 0)
{
v___y_1693_ = v_a_1711_;
v___y_1694_ = v___y_1706_;
v___y_1695_ = v___y_1707_;
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
lean_inc(v_a_1711_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_a_1711_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
lean_inc(v___x_1496_);
v___x_1718_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1496_, v___x_1717_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
v___y_1693_ = v_a_1711_;
v___y_1694_ = v___y_1706_;
v___y_1695_ = v___y_1707_;
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
goto v___jp_1692_;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1711_);
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1711_);
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
v_a_1727_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1712_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1712_);
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
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
lean_dec_ref(v___f_1494_);
v_a_1735_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1710_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1710_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
lean_dec_ref(v___f_1494_);
v_a_1766_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1703_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1703_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
v___jp_1503_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = l_Lean_maxRecDepth;
v___x_1530_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_1507_, v___x_1529_);
lean_inc_ref(v_inheritedTraceOptions_1527_);
lean_inc(v_cancelTk_x3f_1525_);
lean_inc(v_currMacroScope_1524_);
lean_inc(v_quotContext_1523_);
lean_inc(v_maxHeartbeats_1522_);
lean_inc(v_initHeartbeats_1521_);
lean_inc(v_openDecls_1520_);
lean_inc(v_currNamespace_1519_);
lean_inc(v_ref_1518_);
lean_inc(v_currRecDepth_1517_);
lean_inc_ref(v_fileMap_1516_);
lean_inc_ref(v_fileName_1515_);
v___x_1531_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1531_, 0, v_fileName_1515_);
lean_ctor_set(v___x_1531_, 1, v_fileMap_1516_);
lean_ctor_set(v___x_1531_, 2, v___y_1507_);
lean_ctor_set(v___x_1531_, 3, v_currRecDepth_1517_);
lean_ctor_set(v___x_1531_, 4, v___x_1530_);
lean_ctor_set(v___x_1531_, 5, v_ref_1518_);
lean_ctor_set(v___x_1531_, 6, v_currNamespace_1519_);
lean_ctor_set(v___x_1531_, 7, v_openDecls_1520_);
lean_ctor_set(v___x_1531_, 8, v_initHeartbeats_1521_);
lean_ctor_set(v___x_1531_, 9, v_maxHeartbeats_1522_);
lean_ctor_set(v___x_1531_, 10, v_quotContext_1523_);
lean_ctor_set(v___x_1531_, 11, v_currMacroScope_1524_);
lean_ctor_set(v___x_1531_, 12, v_cancelTk_x3f_1525_);
lean_ctor_set(v___x_1531_, 13, v_inheritedTraceOptions_1527_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*14, v___y_1506_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*14 + 1, v_suppressElabErrors_1526_);
v___x_1532_ = l_Lean_MVarId_refl(v___y_1508_, v___y_1511_, v___y_1509_, v___y_1505_, v___x_1531_, v___y_1528_);
lean_dec_ref_known(v___x_1531_, 14);
lean_dec_ref(v___y_1509_);
if (lean_obj_tag(v___x_1532_) == 0)
{
uint8_t v_hasTrace_1533_; 
lean_dec_ref_known(v___x_1532_, 1);
v_hasTrace_1533_ = lean_ctor_get_uint8(v___y_1512_, sizeof(void*)*1);
if (v_hasTrace_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec_ref(v___y_1512_);
lean_dec(v___x_1496_);
v___x_1534_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1495_, v___y_1505_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_1496_);
v___x_1536_ = l_Lean_Name_append(v___x_1535_, v___x_1496_);
v___x_1537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1513_, v___y_1512_, v___x_1536_);
lean_dec(v___x_1536_);
lean_dec_ref(v___y_1512_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec(v___x_1496_);
v___x_1538_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1495_, v___y_1505_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1540_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1496_, v___x_1539_, v___y_1514_, v___y_1505_, v___y_1504_, v___y_1510_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1540_, 1);
v___x_1541_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1495_, v___y_1505_);
return v___x_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_a_1495_);
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
lean_dec_ref(v___y_1512_);
lean_dec(v___x_1496_);
lean_dec_ref(v_a_1495_);
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
lean_object* v_fileName_1572_; lean_object* v_fileMap_1573_; lean_object* v_currRecDepth_1574_; lean_object* v_ref_1575_; lean_object* v_currNamespace_1576_; lean_object* v_openDecls_1577_; lean_object* v_initHeartbeats_1578_; lean_object* v_maxHeartbeats_1579_; lean_object* v_quotContext_1580_; lean_object* v_currMacroScope_1581_; lean_object* v_cancelTk_x3f_1582_; uint8_t v_suppressElabErrors_1583_; lean_object* v_inheritedTraceOptions_1584_; 
v_fileName_1572_ = lean_ctor_get(v___y_1570_, 0);
v_fileMap_1573_ = lean_ctor_get(v___y_1570_, 1);
v_currRecDepth_1574_ = lean_ctor_get(v___y_1570_, 3);
v_ref_1575_ = lean_ctor_get(v___y_1570_, 5);
v_currNamespace_1576_ = lean_ctor_get(v___y_1570_, 6);
v_openDecls_1577_ = lean_ctor_get(v___y_1570_, 7);
v_initHeartbeats_1578_ = lean_ctor_get(v___y_1570_, 8);
v_maxHeartbeats_1579_ = lean_ctor_get(v___y_1570_, 9);
v_quotContext_1580_ = lean_ctor_get(v___y_1570_, 10);
v_currMacroScope_1581_ = lean_ctor_get(v___y_1570_, 11);
v_cancelTk_x3f_1582_ = lean_ctor_get(v___y_1570_, 12);
v_suppressElabErrors_1583_ = lean_ctor_get_uint8(v___y_1570_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1584_ = lean_ctor_get(v___y_1570_, 13);
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
v___y_1514_ = v___y_1569_;
v_fileName_1515_ = v_fileName_1572_;
v_fileMap_1516_ = v_fileMap_1573_;
v_currRecDepth_1517_ = v_currRecDepth_1574_;
v_ref_1518_ = v_ref_1575_;
v_currNamespace_1519_ = v_currNamespace_1576_;
v_openDecls_1520_ = v_openDecls_1577_;
v_initHeartbeats_1521_ = v_initHeartbeats_1578_;
v_maxHeartbeats_1522_ = v_maxHeartbeats_1579_;
v_quotContext_1523_ = v_quotContext_1580_;
v_currMacroScope_1524_ = v_currMacroScope_1581_;
v_cancelTk_x3f_1525_ = v_cancelTk_x3f_1582_;
v_suppressElabErrors_1526_ = v_suppressElabErrors_1583_;
v_inheritedTraceOptions_1527_ = v_inheritedTraceOptions_1584_;
v___y_1528_ = v___y_1571_;
goto v___jp_1503_;
}
v___jp_1585_:
{
if (v___y_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v_env_1599_; lean_object* v_nextMacroScope_1600_; lean_object* v_ngen_1601_; lean_object* v_auxDeclNGen_1602_; lean_object* v_traceState_1603_; lean_object* v_messages_1604_; lean_object* v_infoState_1605_; lean_object* v_snapshotTasks_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1616_; 
v___x_1598_ = lean_st_ref_take(v___y_1593_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
v_nextMacroScope_1600_ = lean_ctor_get(v___x_1598_, 1);
v_ngen_1601_ = lean_ctor_get(v___x_1598_, 2);
v_auxDeclNGen_1602_ = lean_ctor_get(v___x_1598_, 3);
v_traceState_1603_ = lean_ctor_get(v___x_1598_, 4);
v_messages_1604_ = lean_ctor_get(v___x_1598_, 6);
v_infoState_1605_ = lean_ctor_get(v___x_1598_, 7);
v_snapshotTasks_1606_ = lean_ctor_get(v___x_1598_, 8);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v___x_1598_, 5);
lean_dec(v_unused_1617_);
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snapshotTasks_1606_);
lean_inc(v_infoState_1605_);
lean_inc(v_messages_1604_);
lean_inc(v_traceState_1603_);
lean_inc(v_auxDeclNGen_1602_);
lean_inc(v_ngen_1601_);
lean_inc(v_nextMacroScope_1600_);
lean_inc(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = l_Lean_Kernel_enableDiag(v_env_1599_, v___y_1589_);
v___x_1611_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 5, v___x_1611_);
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_nextMacroScope_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_ngen_1601_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_auxDeclNGen_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_traceState_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_messages_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_infoState_1605_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_snapshotTasks_1606_);
v___x_1613_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_st_ref_set(v___y_1593_, v___x_1613_);
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___y_1588_;
v___y_1561_ = v___y_1589_;
v___y_1562_ = v___y_1587_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1593_;
v___y_1566_ = v___y_1592_;
v___y_1567_ = v___y_1594_;
v___y_1568_ = v___y_1596_;
v___y_1569_ = v___y_1595_;
v___y_1570_ = v___y_1586_;
v___y_1571_ = v___y_1593_;
goto v___jp_1558_;
}
}
}
else
{
v___y_1559_ = v___y_1586_;
v___y_1560_ = v___y_1588_;
v___y_1561_ = v___y_1589_;
v___y_1562_ = v___y_1587_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1593_;
v___y_1566_ = v___y_1592_;
v___y_1567_ = v___y_1594_;
v___y_1568_ = v___y_1596_;
v___y_1569_ = v___y_1595_;
v___y_1570_ = v___y_1586_;
v___y_1571_ = v___y_1593_;
goto v___jp_1558_;
}
}
v___jp_1618_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v_foApprox_1628_; uint8_t v_ctxApprox_1629_; uint8_t v_quasiPatternApprox_1630_; uint8_t v_constApprox_1631_; uint8_t v_isDefEqStuckEx_1632_; uint8_t v_unificationHints_1633_; uint8_t v_proofIrrelevance_1634_; uint8_t v_assignSyntheticOpaque_1635_; uint8_t v_offsetCnstrs_1636_; uint8_t v_etaStruct_1637_; uint8_t v_univApprox_1638_; uint8_t v_iota_1639_; uint8_t v_beta_1640_; uint8_t v_proj_1641_; uint8_t v_zeta_1642_; uint8_t v_zetaDelta_1643_; uint8_t v_zetaUnused_1644_; uint8_t v_zetaHave_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1691_; 
v___x_1626_ = lean_st_ref_get(v___y_1623_);
v___x_1627_ = l_Lean_Meta_Context_config(v___y_1624_);
v_foApprox_1628_ = lean_ctor_get_uint8(v___x_1627_, 0);
v_ctxApprox_1629_ = lean_ctor_get_uint8(v___x_1627_, 1);
v_quasiPatternApprox_1630_ = lean_ctor_get_uint8(v___x_1627_, 2);
v_constApprox_1631_ = lean_ctor_get_uint8(v___x_1627_, 3);
v_isDefEqStuckEx_1632_ = lean_ctor_get_uint8(v___x_1627_, 4);
v_unificationHints_1633_ = lean_ctor_get_uint8(v___x_1627_, 5);
v_proofIrrelevance_1634_ = lean_ctor_get_uint8(v___x_1627_, 6);
v_assignSyntheticOpaque_1635_ = lean_ctor_get_uint8(v___x_1627_, 7);
v_offsetCnstrs_1636_ = lean_ctor_get_uint8(v___x_1627_, 8);
v_etaStruct_1637_ = lean_ctor_get_uint8(v___x_1627_, 10);
v_univApprox_1638_ = lean_ctor_get_uint8(v___x_1627_, 11);
v_iota_1639_ = lean_ctor_get_uint8(v___x_1627_, 12);
v_beta_1640_ = lean_ctor_get_uint8(v___x_1627_, 13);
v_proj_1641_ = lean_ctor_get_uint8(v___x_1627_, 14);
v_zeta_1642_ = lean_ctor_get_uint8(v___x_1627_, 15);
v_zetaDelta_1643_ = lean_ctor_get_uint8(v___x_1627_, 16);
v_zetaUnused_1644_ = lean_ctor_get_uint8(v___x_1627_, 17);
v_zetaHave_1645_ = lean_ctor_get_uint8(v___x_1627_, 18);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1647_ = v___x_1627_;
v_isShared_1648_ = v_isSharedCheck_1691_;
goto v_resetjp_1646_;
}
else
{
lean_dec(v___x_1627_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1691_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint8_t v_trackZetaDelta_1649_; lean_object* v_zetaDeltaSet_1650_; lean_object* v_lctx_1651_; lean_object* v_localInstances_1652_; lean_object* v_defEqCtx_x3f_1653_; lean_object* v_synthPendingDepth_1654_; lean_object* v_canUnfold_x3f_1655_; uint8_t v_univApprox_1656_; uint8_t v_inTypeClassResolution_1657_; uint8_t v_cacheInferType_1658_; lean_object* v_fileName_1659_; lean_object* v_fileMap_1660_; lean_object* v_options_1661_; lean_object* v_currRecDepth_1662_; lean_object* v_ref_1663_; lean_object* v_currNamespace_1664_; lean_object* v_openDecls_1665_; lean_object* v_initHeartbeats_1666_; lean_object* v_maxHeartbeats_1667_; lean_object* v_quotContext_1668_; lean_object* v_currMacroScope_1669_; lean_object* v_cancelTk_x3f_1670_; uint8_t v_suppressElabErrors_1671_; lean_object* v_inheritedTraceOptions_1672_; lean_object* v_env_1673_; lean_object* v_config_1675_; 
v_trackZetaDelta_1649_ = lean_ctor_get_uint8(v___y_1624_, sizeof(void*)*7);
v_zetaDeltaSet_1650_ = lean_ctor_get(v___y_1624_, 1);
v_lctx_1651_ = lean_ctor_get(v___y_1624_, 2);
v_localInstances_1652_ = lean_ctor_get(v___y_1624_, 3);
v_defEqCtx_x3f_1653_ = lean_ctor_get(v___y_1624_, 4);
v_synthPendingDepth_1654_ = lean_ctor_get(v___y_1624_, 5);
v_canUnfold_x3f_1655_ = lean_ctor_get(v___y_1624_, 6);
v_univApprox_1656_ = lean_ctor_get_uint8(v___y_1624_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1657_ = lean_ctor_get_uint8(v___y_1624_, sizeof(void*)*7 + 2);
v_cacheInferType_1658_ = lean_ctor_get_uint8(v___y_1624_, sizeof(void*)*7 + 3);
v_fileName_1659_ = lean_ctor_get(v___y_1619_, 0);
v_fileMap_1660_ = lean_ctor_get(v___y_1619_, 1);
v_options_1661_ = lean_ctor_get(v___y_1619_, 2);
v_currRecDepth_1662_ = lean_ctor_get(v___y_1619_, 3);
v_ref_1663_ = lean_ctor_get(v___y_1619_, 5);
v_currNamespace_1664_ = lean_ctor_get(v___y_1619_, 6);
v_openDecls_1665_ = lean_ctor_get(v___y_1619_, 7);
v_initHeartbeats_1666_ = lean_ctor_get(v___y_1619_, 8);
v_maxHeartbeats_1667_ = lean_ctor_get(v___y_1619_, 9);
v_quotContext_1668_ = lean_ctor_get(v___y_1619_, 10);
v_currMacroScope_1669_ = lean_ctor_get(v___y_1619_, 11);
v_cancelTk_x3f_1670_ = lean_ctor_get(v___y_1619_, 12);
v_suppressElabErrors_1671_ = lean_ctor_get_uint8(v___y_1619_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1672_ = lean_ctor_get(v___y_1619_, 13);
v_env_1673_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1673_);
lean_dec(v___x_1626_);
if (v_isShared_1648_ == 0)
{
v_config_1675_ = v___x_1647_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 0, v_foApprox_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 1, v_ctxApprox_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 2, v_quasiPatternApprox_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 3, v_constApprox_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 4, v_isDefEqStuckEx_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 5, v_unificationHints_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 6, v_proofIrrelevance_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 7, v_assignSyntheticOpaque_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 8, v_offsetCnstrs_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 10, v_etaStruct_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 11, v_univApprox_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 12, v_iota_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 13, v_beta_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 14, v_proj_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 15, v_zeta_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 16, v_zetaDelta_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 17, v_zetaUnused_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, 18, v_zetaHave_1645_);
v_config_1675_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
uint64_t v___x_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; uint64_t v___x_1680_; uint64_t v_key_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; uint8_t v___x_1689_; 
lean_ctor_set_uint8(v_config_1675_, 9, v___y_1625_);
v___x_1676_ = l_Lean_Meta_Context_configKey(v___y_1624_);
v___x_1677_ = 3ULL;
v___x_1678_ = lean_uint64_shift_right(v___x_1676_, v___x_1677_);
v___x_1679_ = lean_uint64_shift_left(v___x_1678_, v___x_1677_);
v___x_1680_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1625_);
v_key_1681_ = lean_uint64_lor(v___x_1679_, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1682_, 0, v_config_1675_);
lean_ctor_set_uint64(v___x_1682_, sizeof(void*)*1, v_key_1681_);
lean_inc(v_canUnfold_x3f_1655_);
lean_inc(v_synthPendingDepth_1654_);
lean_inc(v_defEqCtx_x3f_1653_);
lean_inc_ref(v_localInstances_1652_);
lean_inc_ref(v_lctx_1651_);
lean_inc(v_zetaDeltaSet_1650_);
v___x_1683_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v_zetaDeltaSet_1650_);
lean_ctor_set(v___x_1683_, 2, v_lctx_1651_);
lean_ctor_set(v___x_1683_, 3, v_localInstances_1652_);
lean_ctor_set(v___x_1683_, 4, v_defEqCtx_x3f_1653_);
lean_ctor_set(v___x_1683_, 5, v_synthPendingDepth_1654_);
lean_ctor_set(v___x_1683_, 6, v_canUnfold_x3f_1655_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*7, v_trackZetaDelta_1649_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*7 + 1, v_univApprox_1656_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1657_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*7 + 3, v_cacheInferType_1658_);
v___x_1684_ = l_Lean_Meta_smartUnfolding;
v___x_1685_ = 0;
lean_inc_ref(v_options_1661_);
v___x_1686_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1661_, v___x_1684_, v___x_1685_);
v___x_1687_ = l_Lean_diagnostics;
v___x_1688_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1686_, v___x_1687_);
v___x_1689_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1673_);
lean_dec_ref(v_env_1673_);
if (v___x_1689_ == 0)
{
if (v___x_1688_ == 0)
{
lean_inc_ref(v_options_1661_);
v___y_1504_ = v___y_1619_;
v___y_1505_ = v___y_1620_;
v___y_1506_ = v___x_1688_;
v___y_1507_ = v___x_1686_;
v___y_1508_ = v___y_1621_;
v___y_1509_ = v___x_1683_;
v___y_1510_ = v___y_1623_;
v___y_1511_ = v___y_1622_;
v___y_1512_ = v_options_1661_;
v___y_1513_ = v_inheritedTraceOptions_1672_;
v___y_1514_ = v___y_1624_;
v_fileName_1515_ = v_fileName_1659_;
v_fileMap_1516_ = v_fileMap_1660_;
v_currRecDepth_1517_ = v_currRecDepth_1662_;
v_ref_1518_ = v_ref_1663_;
v_currNamespace_1519_ = v_currNamespace_1664_;
v_openDecls_1520_ = v_openDecls_1665_;
v_initHeartbeats_1521_ = v_initHeartbeats_1666_;
v_maxHeartbeats_1522_ = v_maxHeartbeats_1667_;
v_quotContext_1523_ = v_quotContext_1668_;
v_currMacroScope_1524_ = v_currMacroScope_1669_;
v_cancelTk_x3f_1525_ = v_cancelTk_x3f_1670_;
v_suppressElabErrors_1526_ = v_suppressElabErrors_1671_;
v_inheritedTraceOptions_1527_ = v_inheritedTraceOptions_1672_;
v___y_1528_ = v___y_1623_;
goto v___jp_1503_;
}
else
{
lean_inc_ref(v_options_1661_);
v___y_1586_ = v___y_1619_;
v___y_1587_ = v___x_1686_;
v___y_1588_ = v___y_1620_;
v___y_1589_ = v___x_1688_;
v___y_1590_ = v___y_1621_;
v___y_1591_ = v___x_1683_;
v___y_1592_ = v___y_1622_;
v___y_1593_ = v___y_1623_;
v___y_1594_ = v_options_1661_;
v___y_1595_ = v___y_1624_;
v___y_1596_ = v_inheritedTraceOptions_1672_;
v___y_1597_ = v___x_1689_;
goto v___jp_1585_;
}
}
else
{
lean_inc_ref(v_options_1661_);
v___y_1586_ = v___y_1619_;
v___y_1587_ = v___x_1686_;
v___y_1588_ = v___y_1620_;
v___y_1589_ = v___x_1688_;
v___y_1590_ = v___y_1621_;
v___y_1591_ = v___x_1683_;
v___y_1592_ = v___y_1622_;
v___y_1593_ = v___y_1623_;
v___y_1594_ = v_options_1661_;
v___y_1595_ = v___y_1624_;
v___y_1596_ = v_inheritedTraceOptions_1672_;
v___y_1597_ = v___x_1688_;
goto v___jp_1585_;
}
}
}
}
v___jp_1692_:
{
lean_object* v___x_1698_; uint8_t v_transparency_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; 
v___x_1698_ = l_Lean_Meta_Context_config(v___y_1694_);
v_transparency_1699_ = lean_ctor_get_uint8(v___x_1698_, 9);
lean_dec_ref(v___x_1698_);
v___x_1700_ = 0;
v___x_1701_ = 1;
v___x_1702_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1699_, v___x_1700_);
if (v___x_1702_ == 0)
{
v___y_1619_ = v___y_1696_;
v___y_1620_ = v___y_1695_;
v___y_1621_ = v___y_1693_;
v___y_1622_ = v___x_1701_;
v___y_1623_ = v___y_1697_;
v___y_1624_ = v___y_1694_;
v___y_1625_ = v_transparency_1699_;
goto v___jp_1618_;
}
else
{
v___y_1619_ = v___y_1696_;
v___y_1620_ = v___y_1695_;
v___y_1621_ = v___y_1693_;
v___y_1622_ = v___x_1701_;
v___y_1623_ = v___y_1697_;
v___y_1624_ = v___y_1694_;
v___y_1625_ = v___x_1700_;
goto v___jp_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1774_, lean_object* v_declNameNonRec_1775_, lean_object* v___x_1776_, lean_object* v___f_1777_, lean_object* v_a_1778_, lean_object* v___x_1779_, lean_object* v_____r_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1774_, v_declNameNonRec_1775_, v___x_1776_, v___f_1777_, v_a_1778_, v___x_1779_, v_____r_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1786_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_declName_1804_, lean_object* v_a_1805_, lean_object* v___x_1806_, lean_object* v_declNameNonRec_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___y_1814_; lean_object* v___y_1815_; uint8_t v___y_1816_; lean_object* v___y_1826_; lean_object* v_a_1827_; lean_object* v___y_1831_; lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1805_, v___x_1806_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___f_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1862_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6));
v___f_1836_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7));
v___x_1837_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1835_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = l_Lean_Expr_mvarId_x21(v_a_1834_);
v___x_1843_ = lean_unbox(v_a_1838_);
lean_dec(v_a_1838_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_del_object(v___x_1840_);
v___x_1844_ = lean_box(0);
lean_inc(v_declName_1804_);
v___x_1845_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1804_, v_declNameNonRec_1807_, v___x_1842_, v___f_1836_, v_a_1834_, v___x_1835_, v___x_1844_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
v___y_1831_ = v___x_1845_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
lean_inc(v___x_1842_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 1);
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1848_ = v___x_1840_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1842_);
v___x_1848_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1846_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1835_, v___x_1849_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
lean_inc(v_declName_1804_);
v___x_1852_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1804_, v_declNameNonRec_1807_, v___x_1842_, v___f_1836_, v_a_1834_, v___x_1835_, v_a_1851_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
v___y_1831_ = v___x_1852_;
goto v___jp_1830_;
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v___x_1842_);
lean_dec(v_a_1834_);
lean_dec(v_declNameNonRec_1807_);
v_a_1853_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1850_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1850_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
lean_inc(v_a_1853_);
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
v___y_1826_ = v___x_1858_;
v_a_1827_ = v_a_1853_;
goto v___jp_1825_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1807_);
v___y_1831_ = v___x_1833_;
goto v___jp_1830_;
}
v___jp_1813_:
{
if (v___y_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v___y_1814_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_1818_ = l_Lean_MessageData_ofConstName(v_declName_1804_, v___y_1816_);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_Exception_toMessageData(v___y_1815_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1823_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1824_;
}
else
{
lean_dec_ref(v___y_1815_);
lean_dec(v_declName_1804_);
return v___y_1814_;
}
}
v___jp_1825_:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Lean_Exception_isInterrupt(v_a_1827_);
if (v___x_1828_ == 0)
{
uint8_t v___x_1829_; 
lean_inc_ref(v_a_1827_);
v___x_1829_ = l_Lean_Exception_isRuntime(v_a_1827_);
v___y_1814_ = v___y_1826_;
v___y_1815_ = v_a_1827_;
v___y_1816_ = v___x_1829_;
goto v___jp_1813_;
}
else
{
v___y_1814_ = v___y_1826_;
v___y_1815_ = v_a_1827_;
v___y_1816_ = v___x_1828_;
goto v___jp_1813_;
}
}
v___jp_1830_:
{
if (lean_obj_tag(v___y_1831_) == 0)
{
lean_dec(v_declName_1804_);
return v___y_1831_;
}
else
{
lean_object* v_a_1832_; 
v_a_1832_ = lean_ctor_get(v___y_1831_, 0);
lean_inc(v_a_1832_);
v___y_1826_ = v___y_1831_;
v_a_1827_ = v_a_1832_;
goto v___jp_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_declName_1863_, lean_object* v_a_1864_, lean_object* v___x_1865_, lean_object* v_declNameNonRec_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_1863_, v_a_1864_, v___x_1865_, v_declNameNonRec_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = l_List_reverse___redArg(v_a_1874_);
return v___x_1875_;
}
else
{
lean_object* v_head_1876_; lean_object* v_tail_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1886_; 
v_head_1876_ = lean_ctor_get(v_a_1873_, 0);
v_tail_1877_ = lean_ctor_get(v_a_1873_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1873_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1879_ = v_a_1873_;
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_tail_1877_);
lean_inc(v_head_1876_);
lean_dec(v_a_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_mkLevelParam(v_head_1876_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_a_1874_);
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1874_);
v___x_1883_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
v_a_1873_ = v_tail_1877_;
v_a_1874_ = v___x_1883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_levelParams_1887_, lean_object* v_declName_1888_, lean_object* v_declNameNonRec_1889_, lean_object* v_name_1890_, lean_object* v_xs_1891_, lean_object* v_body_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; lean_object* v_us_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1898_ = lean_box(0);
lean_inc(v_levelParams_1887_);
v_us_1899_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1887_, v___x_1898_);
lean_inc(v_declName_1888_);
v___x_1900_ = l_Lean_mkConst(v_declName_1888_, v_us_1899_);
v___x_1901_ = l_Lean_mkAppN(v___x_1900_, v_xs_1891_);
v___x_1902_ = l_Lean_Meta_mkEq(v___x_1901_, v_body_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc_n(v_a_1903_, 2);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = lean_box(0);
v___f_1905_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1905_, 0, v_declName_1888_);
lean_closure_set(v___f_1905_, 1, v_a_1903_);
lean_closure_set(v___f_1905_, 2, v___x_1904_);
lean_closure_set(v___f_1905_, 3, v_declNameNonRec_1889_);
v___x_1906_ = 0;
v___x_1907_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_1905_, v___x_1906_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; uint8_t v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = 1;
v___x_1910_ = 1;
v___x_1911_ = l_Lean_Meta_mkForallFVars(v_xs_1891_, v_a_1903_, v___x_1906_, v___x_1909_, v___x_1909_, v___x_1910_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_Meta_letToHave(v_a_1912_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Meta_mkLambdaFVars(v_xs_1891_, v_a_1908_, v___x_1906_, v___x_1909_, v___x_1906_, v___x_1909_, v___x_1910_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
lean_inc(v_name_1890_);
v___x_1917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1917_, 0, v_name_1890_);
lean_ctor_set(v___x_1917_, 1, v_levelParams_1887_);
lean_ctor_set(v___x_1917_, 2, v_a_1914_);
v___x_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_name_1890_);
lean_ctor_set(v___x_1918_, 1, v___x_1898_);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v_a_1916_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
v___x_1920_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_1919_, v___y_1896_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = l_Lean_addDecl(v_a_1921_, v___x_1906_, v___y_1895_, v___y_1896_);
return v___x_1922_;
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_a_1914_);
lean_dec(v_name_1890_);
lean_dec(v_levelParams_1887_);
v_a_1923_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1915_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1915_);
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
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1908_);
lean_dec(v_name_1890_);
lean_dec(v_levelParams_1887_);
v_a_1931_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1913_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1913_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_a_1908_);
lean_dec(v_name_1890_);
lean_dec(v_levelParams_1887_);
v_a_1939_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1911_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1911_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_a_1903_);
lean_dec(v_name_1890_);
lean_dec(v_levelParams_1887_);
v_a_1947_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1907_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1907_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_name_1890_);
lean_dec(v_declNameNonRec_1889_);
lean_dec(v_declName_1888_);
lean_dec(v_levelParams_1887_);
v_a_1955_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1902_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1902_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_levelParams_1963_, lean_object* v_declName_1964_, lean_object* v_declNameNonRec_1965_, lean_object* v_name_1966_, lean_object* v_xs_1967_, lean_object* v_body_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_1963_, v_declName_1964_, v_declNameNonRec_1965_, v_name_1966_, v_xs_1967_, v_body_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec_ref(v_xs_1967_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1975_, lean_object* v_info_1976_, lean_object* v_name_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v_levelParams_1984_; lean_object* v_value_1985_; lean_object* v_declNameNonRec_1986_; lean_object* v_fileName_1987_; lean_object* v_fileMap_1988_; lean_object* v_options_1989_; lean_object* v_currRecDepth_1990_; lean_object* v_ref_1991_; lean_object* v_currNamespace_1992_; lean_object* v_openDecls_1993_; lean_object* v_initHeartbeats_1994_; lean_object* v_maxHeartbeats_1995_; lean_object* v_quotContext_1996_; lean_object* v_currMacroScope_1997_; lean_object* v_cancelTk_x3f_1998_; uint8_t v_suppressElabErrors_1999_; lean_object* v_inheritedTraceOptions_2000_; lean_object* v_env_2001_; lean_object* v___f_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v_fileName_2009_; lean_object* v_fileMap_2010_; lean_object* v_currRecDepth_2011_; lean_object* v_ref_2012_; lean_object* v_currNamespace_2013_; lean_object* v_openDecls_2014_; lean_object* v_initHeartbeats_2015_; lean_object* v_maxHeartbeats_2016_; lean_object* v_quotContext_2017_; lean_object* v_currMacroScope_2018_; lean_object* v_cancelTk_x3f_2019_; uint8_t v_suppressElabErrors_2020_; lean_object* v_inheritedTraceOptions_2021_; lean_object* v___y_2022_; uint8_t v___y_2028_; uint8_t v___x_2049_; 
v___x_1983_ = lean_st_ref_get(v_a_1981_);
v_levelParams_1984_ = lean_ctor_get(v_info_1976_, 1);
lean_inc(v_levelParams_1984_);
v_value_1985_ = lean_ctor_get(v_info_1976_, 3);
lean_inc_ref(v_value_1985_);
v_declNameNonRec_1986_ = lean_ctor_get(v_info_1976_, 5);
lean_inc(v_declNameNonRec_1986_);
lean_dec_ref(v_info_1976_);
v_fileName_1987_ = lean_ctor_get(v_a_1980_, 0);
v_fileMap_1988_ = lean_ctor_get(v_a_1980_, 1);
v_options_1989_ = lean_ctor_get(v_a_1980_, 2);
v_currRecDepth_1990_ = lean_ctor_get(v_a_1980_, 3);
v_ref_1991_ = lean_ctor_get(v_a_1980_, 5);
v_currNamespace_1992_ = lean_ctor_get(v_a_1980_, 6);
v_openDecls_1993_ = lean_ctor_get(v_a_1980_, 7);
v_initHeartbeats_1994_ = lean_ctor_get(v_a_1980_, 8);
v_maxHeartbeats_1995_ = lean_ctor_get(v_a_1980_, 9);
v_quotContext_1996_ = lean_ctor_get(v_a_1980_, 10);
v_currMacroScope_1997_ = lean_ctor_get(v_a_1980_, 11);
v_cancelTk_x3f_1998_ = lean_ctor_get(v_a_1980_, 12);
v_suppressElabErrors_1999_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2000_ = lean_ctor_get(v_a_1980_, 13);
v_env_2001_ = lean_ctor_get(v___x_1983_, 0);
lean_inc_ref(v_env_2001_);
lean_dec(v___x_1983_);
v___f_2002_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2002_, 0, v_levelParams_1984_);
lean_closure_set(v___f_2002_, 1, v_declName_1975_);
lean_closure_set(v___f_2002_, 2, v_declNameNonRec_1986_);
lean_closure_set(v___f_2002_, 3, v_name_1977_);
v___x_2003_ = 0;
v___x_2004_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_1989_);
v___x_2005_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1989_, v___x_2004_, v___x_2003_);
v___x_2006_ = l_Lean_diagnostics;
v___x_2007_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_2005_, v___x_2006_);
v___x_2049_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2001_);
lean_dec_ref(v_env_2001_);
if (v___x_2049_ == 0)
{
if (v___x_2007_ == 0)
{
v_fileName_2009_ = v_fileName_1987_;
v_fileMap_2010_ = v_fileMap_1988_;
v_currRecDepth_2011_ = v_currRecDepth_1990_;
v_ref_2012_ = v_ref_1991_;
v_currNamespace_2013_ = v_currNamespace_1992_;
v_openDecls_2014_ = v_openDecls_1993_;
v_initHeartbeats_2015_ = v_initHeartbeats_1994_;
v_maxHeartbeats_2016_ = v_maxHeartbeats_1995_;
v_quotContext_2017_ = v_quotContext_1996_;
v_currMacroScope_2018_ = v_currMacroScope_1997_;
v_cancelTk_x3f_2019_ = v_cancelTk_x3f_1998_;
v_suppressElabErrors_2020_ = v_suppressElabErrors_1999_;
v_inheritedTraceOptions_2021_ = v_inheritedTraceOptions_2000_;
v___y_2022_ = v_a_1981_;
goto v___jp_2008_;
}
else
{
v___y_2028_ = v___x_2049_;
goto v___jp_2027_;
}
}
else
{
v___y_2028_ = v___x_2007_;
goto v___jp_2027_;
}
v___jp_2008_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = l_Lean_maxRecDepth;
v___x_2024_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_2005_, v___x_2023_);
lean_inc_ref(v_inheritedTraceOptions_2021_);
lean_inc(v_cancelTk_x3f_2019_);
lean_inc(v_currMacroScope_2018_);
lean_inc(v_quotContext_2017_);
lean_inc(v_maxHeartbeats_2016_);
lean_inc(v_initHeartbeats_2015_);
lean_inc(v_openDecls_2014_);
lean_inc(v_currNamespace_2013_);
lean_inc(v_ref_2012_);
lean_inc(v_currRecDepth_2011_);
lean_inc_ref(v_fileMap_2010_);
lean_inc_ref(v_fileName_2009_);
v___x_2025_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2025_, 0, v_fileName_2009_);
lean_ctor_set(v___x_2025_, 1, v_fileMap_2010_);
lean_ctor_set(v___x_2025_, 2, v___x_2005_);
lean_ctor_set(v___x_2025_, 3, v_currRecDepth_2011_);
lean_ctor_set(v___x_2025_, 4, v___x_2024_);
lean_ctor_set(v___x_2025_, 5, v_ref_2012_);
lean_ctor_set(v___x_2025_, 6, v_currNamespace_2013_);
lean_ctor_set(v___x_2025_, 7, v_openDecls_2014_);
lean_ctor_set(v___x_2025_, 8, v_initHeartbeats_2015_);
lean_ctor_set(v___x_2025_, 9, v_maxHeartbeats_2016_);
lean_ctor_set(v___x_2025_, 10, v_quotContext_2017_);
lean_ctor_set(v___x_2025_, 11, v_currMacroScope_2018_);
lean_ctor_set(v___x_2025_, 12, v_cancelTk_x3f_2019_);
lean_ctor_set(v___x_2025_, 13, v_inheritedTraceOptions_2021_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*14, v___x_2007_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*14 + 1, v_suppressElabErrors_2020_);
v___x_2026_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_1985_, v___f_2002_, v___x_2003_, v_a_1978_, v_a_1979_, v___x_2025_, v___y_2022_);
lean_dec_ref_known(v___x_2025_, 14);
return v___x_2026_;
}
v___jp_2027_:
{
if (v___y_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v_env_2030_; lean_object* v_nextMacroScope_2031_; lean_object* v_ngen_2032_; lean_object* v_auxDeclNGen_2033_; lean_object* v_traceState_2034_; lean_object* v_messages_2035_; lean_object* v_infoState_2036_; lean_object* v_snapshotTasks_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v___x_2029_ = lean_st_ref_take(v_a_1981_);
v_env_2030_ = lean_ctor_get(v___x_2029_, 0);
v_nextMacroScope_2031_ = lean_ctor_get(v___x_2029_, 1);
v_ngen_2032_ = lean_ctor_get(v___x_2029_, 2);
v_auxDeclNGen_2033_ = lean_ctor_get(v___x_2029_, 3);
v_traceState_2034_ = lean_ctor_get(v___x_2029_, 4);
v_messages_2035_ = lean_ctor_get(v___x_2029_, 6);
v_infoState_2036_ = lean_ctor_get(v___x_2029_, 7);
v_snapshotTasks_2037_ = lean_ctor_get(v___x_2029_, 8);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2029_, 5);
lean_dec(v_unused_2048_);
v___x_2039_ = v___x_2029_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_snapshotTasks_2037_);
lean_inc(v_infoState_2036_);
lean_inc(v_messages_2035_);
lean_inc(v_traceState_2034_);
lean_inc(v_auxDeclNGen_2033_);
lean_inc(v_ngen_2032_);
lean_inc(v_nextMacroScope_2031_);
lean_inc(v_env_2030_);
lean_dec(v___x_2029_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = l_Lean_Kernel_enableDiag(v_env_2030_, v___x_2007_);
v___x_2042_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 5, v___x_2042_);
lean_ctor_set(v___x_2039_, 0, v___x_2041_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_nextMacroScope_2031_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_ngen_2032_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_auxDeclNGen_2033_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v_traceState_2034_);
lean_ctor_set(v_reuseFailAlloc_2046_, 5, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2046_, 6, v_messages_2035_);
lean_ctor_set(v_reuseFailAlloc_2046_, 7, v_infoState_2036_);
lean_ctor_set(v_reuseFailAlloc_2046_, 8, v_snapshotTasks_2037_);
v___x_2044_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_st_ref_set(v_a_1981_, v___x_2044_);
v_fileName_2009_ = v_fileName_1987_;
v_fileMap_2010_ = v_fileMap_1988_;
v_currRecDepth_2011_ = v_currRecDepth_1990_;
v_ref_2012_ = v_ref_1991_;
v_currNamespace_2013_ = v_currNamespace_1992_;
v_openDecls_2014_ = v_openDecls_1993_;
v_initHeartbeats_2015_ = v_initHeartbeats_1994_;
v_maxHeartbeats_2016_ = v_maxHeartbeats_1995_;
v_quotContext_2017_ = v_quotContext_1996_;
v_currMacroScope_2018_ = v_currMacroScope_1997_;
v_cancelTk_x3f_2019_ = v_cancelTk_x3f_1998_;
v_suppressElabErrors_2020_ = v_suppressElabErrors_1999_;
v_inheritedTraceOptions_2021_ = v_inheritedTraceOptions_2000_;
v___y_2022_ = v_a_1981_;
goto v___jp_2008_;
}
}
}
else
{
v_fileName_2009_ = v_fileName_1987_;
v_fileMap_2010_ = v_fileMap_1988_;
v_currRecDepth_2011_ = v_currRecDepth_1990_;
v_ref_2012_ = v_ref_1991_;
v_currNamespace_2013_ = v_currNamespace_1992_;
v_openDecls_2014_ = v_openDecls_1993_;
v_initHeartbeats_2015_ = v_initHeartbeats_1994_;
v_maxHeartbeats_2016_ = v_maxHeartbeats_1995_;
v_quotContext_2017_ = v_quotContext_1996_;
v_currMacroScope_2018_ = v_currMacroScope_1997_;
v_cancelTk_x3f_2019_ = v_cancelTk_x3f_1998_;
v_suppressElabErrors_2020_ = v_suppressElabErrors_1999_;
v_inheritedTraceOptions_2021_ = v_inheritedTraceOptions_2000_;
v___y_2022_ = v_a_1981_;
goto v___jp_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2050_, lean_object* v_info_2051_, lean_object* v_name_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2050_, v_info_2051_, v_name_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2059_, lean_object* v_info_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v_env_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = lean_st_ref_get(v_a_2064_);
v_env_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_2059_, 2);
v___x_2069_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2067_, v_declName_2059_, v___x_2068_);
lean_inc_n(v___x_2069_, 2);
v___x_2070_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2070_, 0, v_declName_2059_);
lean_closure_set(v___x_2070_, 1, v_info_2060_);
lean_closure_set(v___x_2070_, 2, v___x_2069_);
v___x_2071_ = l_Lean_Meta_realizeConst(v_declName_2059_, v___x_2069_, v___x_2070_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2079_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2069_);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2069_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v___x_2069_);
v_a_2080_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2088_, lean_object* v_info_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2088_, v_info_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_env_2104_; lean_object* v_env_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2102_ = lean_st_ref_get(v_a_2100_);
v___x_2103_ = lean_st_ref_get(v_a_2100_);
v_env_2104_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_env_2104_);
lean_dec(v___x_2102_);
v_env_2105_ = lean_ctor_get(v___x_2103_, 0);
lean_inc_ref_n(v_env_2105_, 2);
lean_dec(v___x_2103_);
v___x_2106_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2096_);
v___x_2107_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2104_, v_declName_2096_, v___x_2106_);
v___x_2108_ = 1;
lean_inc(v___x_2107_);
v___x_2109_ = l_Lean_Environment_contains(v_env_2105_, v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v_toEnvExtension_2111_; lean_object* v_asyncMode_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v___x_2107_);
v___x_2110_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2111_ = lean_ctor_get(v___x_2110_, 0);
v_asyncMode_2112_ = lean_ctor_get(v_toEnvExtension_2111_, 2);
v___x_2113_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2114_ = 0;
lean_inc(v_declName_2096_);
v___x_2115_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2113_, v___x_2110_, v_env_2105_, v_declName_2096_, v_asyncMode_2112_, v___x_2114_);
if (lean_obj_tag(v___x_2115_) == 1)
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2140_; 
v_val_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2140_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2140_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2096_, v_val_2116_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2131_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_a_2121_);
v___x_2126_ = v___x_2118_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2126_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2118_);
v_a_2132_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2120_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2120_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
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
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v___x_2115_);
lean_dec(v_declName_2096_);
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v_env_2105_);
lean_dec(v_declName_2096_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2107_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2155_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2157_;
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
